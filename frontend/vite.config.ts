import { defineConfig, loadEnv } from 'vite';
import react from '@vitejs/plugin-react';
import path from 'path'; // This import will now work correctly

// https://vitejs.dev/config/
export default defineConfig(({ mode }) => {
  // Load env file based on `mode` in the current working directory.
  // The third parameter '' makes all environment variables available, 
  // even those without the VITE_ prefix.
  const env = loadEnv(mode, process.cwd(), '');

  return {
    plugins: [react()],
    // --- FIXED: Define environment variables for the client ---
    define: {
      // This makes the environment variables available in your client-side code
      'process.env.GEMINI_API_KEY': JSON.stringify(env.GEMINI_API_KEY)
    },
    // --- FIXED: Set up path aliases ---
    resolve: {
      alias: {
        // This allows you to use '@' as an alias for the 'src' directory
        '@': path.resolve(__dirname, './'),
      },
    },
    server: {
      port: 5173, // Keep the port consistent
      proxy: {
        // Proxy API requests to the Flask backend
        '/api': {
          target: 'http://127.0.0.1:5000',
          changeOrigin: true,
          secure: false,
        },
      },
    },
  };
});
