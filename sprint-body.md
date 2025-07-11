## 📌 Master Checklist
- [x] #11 Warm-Up & Lean Cache Bootstrap
- [x] #12 LeanBuildManager + LRU Cache
- [x] #13 Resilient `call_gemini` + local stub
- [ ] #14 **Deep-Research Scan – Multilingual Sentiment Models** 🔬 @Peter  
  - [ ] Pre-filter HF API script  
  - [ ] Gather F1 / latency / license into CSV  
  - [ ] Score with composite metric  
- [ ] #15 Integrate chosen Tone Model (ONNX) 🎯 @Alex  
- [ ] #16 Front-End Tone Border UI 🎨 @Alex  
- [ ] #17 Persistence MVP (SQLModel + Alembic) 🗄️ @Akira  

```mermaid
gantt
dateFormat YYYY-MM-DD
title Sprint Snapshot 2025-07-08 to 2025-07-15
section Backend
Warm_Up_Cache          :done,   warmup,   2025-07-06, 1d
LeanBuildManager       :done,   lbm,      2025-07-06, 1d
call_gemini_Resilience :done,   gemini,   2025-07-07, 0.5d
Tone_Estimator         :active, tone,     2025-07-09, 2d
section Research
Deep_Scan              :active, scan,     2025-07-08, 2d
Benchmark_Candidates   :future, bench,    after scan, 1d
section Front-End
Spinner_UX             :done,   spin,     2025-07-06, 0.5d
Tone_Border_UI         :blocked,toneui,   after tone, 0.5d
```
