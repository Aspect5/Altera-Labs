import json
import subprocess
import tarfile
import threading
import time
import urllib.error
from pathlib import Path
from unittest.mock import MagicMock, call

import pytest
import requests

# We import the modules to be tested
from backend import app as flask_app
from backend import bootstrap_lean_cache
from backend import local_llm_stub

# --- Test Setup ---

@pytest.fixture
def mock_bootstrap_paths(mocker):
    """
    Safely mocks specific Path objects ONLY within the bootstrap_lean_cache module.
    This avoids breaking pytest's internal use of pathlib.
    """
    # Mock the specific Path objects our script uses.
    build_dir_mock = MagicMock(spec=Path)
    build_dir_mock.exists.return_value = False  # Default to "cache does not exist"
    mocker.patch.object(bootstrap_lean_cache, 'BUILD_DIR', build_dir_mock)

    tmp_archive_mock = MagicMock(spec=Path)
    mocker.patch.object(bootstrap_lean_cache, 'TMP_ARCHIVE', tmp_archive_mock)

    # Also mock PROJECT_ROOT to prevent subprocess from using a real path.
    mocker.patch.object(bootstrap_lean_cache, 'PROJECT_ROOT', 'fake/project/root')
    
    return build_dir_mock, tmp_archive_mock


# --- Feature #11: Warm-Up & Lean Cache Bootstrap ---

class TestBootstrapLeanCache:
    def test_cache_already_present(self, capsys, mock_bootstrap_paths):
        """If BUILD_DIR exists, the script should do nothing and exit."""
        build_dir_mock, _ = mock_bootstrap_paths
        build_dir_mock.exists.return_value = True
        
        bootstrap_lean_cache.main()
        
        captured = capsys.readouterr()
        assert "[LeanCache] cache already present ✔" in captured.out
    
    def test_success_on_first_mirror(self, mocker, capsys, mock_bootstrap_paths):
        """Should download and unpack from the first available mirror."""
        # Mock external calls
        mock_resolve: MagicMock = mocker.patch('backend.bootstrap_lean_cache._resolve', return_value="http://good-mirror.com/cache.tar.xz")
        mock_download: MagicMock = mocker.patch('backend.bootstrap_lean_cache._download', return_value=True)
        mock_unpack: MagicMock = mocker.patch('backend.bootstrap_lean_cache._unpack')

        bootstrap_lean_cache.main()

        # Assertions
        mock_resolve.assert_called_once()
        mock_download.assert_called_once_with("http://good-mirror.com/cache.tar.xz")
        mock_unpack.assert_called_once()
        
        captured = capsys.readouterr()
        assert "[LeanCache] cache ready ✔" in captured.out
        assert "compiling from source" not in captured.out

    def test_fallback_to_second_mirror(self, mocker, capsys, mock_bootstrap_paths):
        """If first mirror fails download, it should try the second."""
        mock_mirror_1: MagicMock = mocker.MagicMock(return_value="http://bad-mirror.com/cache.tar.xz")
        mock_mirror_2: MagicMock = mocker.MagicMock(return_value="http://good-mirror.com/cache.tar.xz")
        mocker.patch('backend.bootstrap_lean_cache.MIRRORS', [mock_mirror_1, mock_mirror_2])

        mock_download: MagicMock = mocker.patch('backend.bootstrap_lean_cache._download', side_effect=[False, True])
        mock_unpack: MagicMock = mocker.patch('backend.bootstrap_lean_cache._unpack')
        
        bootstrap_lean_cache.main()
        
        assert mock_download.call_count == 2
        mock_unpack.assert_called_once()
        assert "[LeanCache] cache ready ✔" in capsys.readouterr().out

    def test_fallback_to_lake_build(self, mocker, capsys, mock_bootstrap_paths):
        """If all mirrors fail, it should fall back to `lake build`."""
        mocker.patch('backend.bootstrap_lean_cache._resolve', return_value="http://bad-mirror.com/cache.tar.xz")
        mocker.patch('backend.bootstrap_lean_cache._download', return_value=False)
        mock_run: MagicMock = mocker.patch('subprocess.run')

        bootstrap_lean_cache.main()
        
        captured = capsys.readouterr()
        assert "all mirrors failed" in captured.out
        mock_run.assert_called_once_with(["lake", "build"], cwd='fake/project/root', check=True)

    def test_unpack_failure_continues_to_next_mirror(self, mocker, capsys, mock_bootstrap_paths):
        """If download succeeds but unpack fails, it should not stop, but try the next mirror."""
        mock_mirror_1: MagicMock = mocker.MagicMock(return_value="http://mirror-with-bad-archive.com/cache.tar.xz")
        mock_mirror_2: MagicMock = mocker.MagicMock(return_value="http://good-mirror.com/cache.tar.xz")
        mocker.patch('backend.bootstrap_lean_cache.MIRRORS', [mock_mirror_1, mock_mirror_2])
        
        mock_download: MagicMock = mocker.patch('backend.bootstrap_lean_cache._download', side_effect=[True, True])
        mock_unpack: MagicMock = mocker.patch('backend.bootstrap_lean_cache._unpack', side_effect=[tarfile.ReadError("bad archive"), None])
        
        bootstrap_lean_cache.main()
        
        captured = capsys.readouterr().out
        assert mock_download.call_count == 2
        assert mock_unpack.call_count == 2
        assert "unpack failed: bad archive" in captured
        assert "[LeanCache] cache ready ✔" in captured


# --- Feature #12: LeanBuildManager + LRU Cache ---

class TestLeanBuildManager:
    @pytest.fixture(autouse=True)
    def clear_cache(self):
        """Ensures the LRU cache is cleared before each test."""
        flask_app.LeanBuildManager._cached_build.cache_clear()

    def test_verify_caches_result(self, mocker):
        """Identical code should only trigger one build; the second call should be cached."""
        mock_run_lean: MagicMock = mocker.patch('backend.app._run_lean_verifier', return_value=(True, "Success"))
        
        code = "theorem test : 1 + 1 = 2 := rfl"
        
        res1_success, res1_msg = flask_app.LeanBuildManager.verify(code)
        res2_success, res2_msg = flask_app.LeanBuildManager.verify(code)
        
        assert res1_success is True and res1_msg == "Success"
        assert res2_success is True and res2_msg == "Success"
        mock_run_lean.assert_called_once_with(code)

    def test_verify_does_not_cache_different_code(self, mocker):
        """Different code submissions should trigger separate builds."""
        mock_run_lean: MagicMock = mocker.patch('backend.app._run_lean_verifier', return_value=(True, "Success"))
        
        code1 = "theorem test1 : 1 + 1 = 2 := rfl"
        code2 = "theorem test2 : 2 + 2 = 4 := rfl"
        
        flask_app.LeanBuildManager.verify(code1)
        flask_app.LeanBuildManager.verify(code2)
        
        assert mock_run_lean.call_count == 2
        mock_run_lean.assert_has_calls([call(code1), call(code2)])

    def test_lock_serialization(self, mocker):
        """Test that the lock's context manager is used."""
        mock_lock_instance = MagicMock()
        mocker.patch('threading.Lock', return_value=mock_lock_instance)
        
        # This re-instantiation is conceptual; we patch the existing lock
        flask_app.LeanBuildManager._lock = threading.Lock()
        
        mocker.patch('backend.app._run_lean_verifier', return_value=(True, "Success"))
        flask_app.LeanBuildManager.verify("code")
        
        # Check that the lock was used as a context manager
        mock_lock_instance.__enter__.assert_called_once()
        mock_lock_instance.__exit__.assert_called_once()
        

# --- Feature #13: Resilient `call_gemini` + local stub ---

class TestCallGemini:
    @pytest.fixture
    def mock_requests(self, mocker):
        """Mocks requests.Session for network calls."""
        mock_session: MagicMock = mocker.patch('requests.Session', autospec=True)
        return mock_session

    def test_no_api_key_falls_back_to_local_stub(self, monkeypatch, mock_requests):
        """If GEMINI_API_KEY is not set, it should immediately use the local stub."""
        monkeypatch.setenv("GEMINI_API_KEY", "")
        
        result = flask_app.call_gemini("prompt")
        
        assert isinstance(result, str)
        mock_requests().post.assert_not_called()

    def test_success_on_first_try_text(self, monkeypatch, mock_requests):
        """Should return text from the first successful API call."""
        monkeypatch.setenv("GEMINI_API_KEY", "fake-key")
        
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = {
            "candidates": [{"content": {"parts": [{"text": "Hello from Gemini"}]}}]
        }
        mock_requests().post.return_value = mock_response
        
        result = flask_app.call_gemini("prompt")
        
        assert result == "Hello from Gemini"
        mock_requests().post.assert_called_once()
    
    def test_success_on_first_try_json(self, monkeypatch, mock_requests):
        """Should return a dict from the first successful API call if is_json_output=True."""
        monkeypatch.setenv("GEMINI_API_KEY", "fake-key")

        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = {"key": "value"}
        mock_requests().post.return_value = mock_response
        
        result = flask_app.call_gemini("prompt", is_json_output=True)
        
        assert result == {"key": "value"}
        _, kwargs = mock_requests().post.call_args
        assert kwargs['json']['generationConfig']['responseMimeType'] == 'application/json'

    def test_api_http_error_fallback_through_models(self, monkeypatch, mock_requests):
        """Should try other models/versions if one returns an HTTP error."""
        monkeypatch.setenv("GEMINI_API_KEY", "fake-key")
        
        fail_response = MagicMock(status_code=500)
        success_response = MagicMock(status_code=200)
        success_response.json.return_value = {
            "candidates": [{"content": {"parts": [{"text": "Success on second try"}]}}]
        }
        mock_requests().post.side_effect = [fail_response, success_response]
        
        result = flask_app.call_gemini("prompt")
        
        assert result == "Success on second try"
        assert mock_requests().post.call_count == 2
    
    def test_all_api_endpoints_fail_falls_back_to_local_stub(self, monkeypatch, mock_requests, capsys, mocker):
        """If all API endpoints fail, it should fall back to the local stub."""
        monkeypatch.setenv("GEMINI_API_KEY", "fake-key")

        mock_requests().post.side_effect = requests.exceptions.RequestException("Connection failed")
        
        # OLD, WRONG WAY: mocker.patch('backend.local_llm_stub.generate_response', ...)
        # CORRECT WAY: Patch the 'local_llm' alias as it exists inside the 'flask_app' module.
        mocker.patch.object(flask_app, 'local_llm', return_value="local stub to the rescue")

        result = flask_app.call_gemini("prompt")

        assert result == "local stub to the rescue"
        assert mock_requests().post.call_count == len(flask_app._GEMINI_MODELS) * len(flask_app._GEMINI_VERSIONS)

        captured = capsys.readouterr()
        assert "[GeminiFallback] all endpoints unreachable" in captured.out