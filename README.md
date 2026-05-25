# Don't LEAN On Me

**How Covert Proof-checker Failures Eradicate 'Formal-Verification'-powered Agentic Guardrails**

> Arka Dash · Carlos José Duarte Casillas · Rishab Kumar Jha · Yatharth Maheshwari · Aditya Bansal  
> *With Apart Research*

[![Lean](https://img.shields.io/badge/Lean-v4.30.0--rc2-blue)](https://lean-lang.org)
[![Paper](https://img.shields.io/badge/Paper-GitHub%20Pages-green)](https://r34l-rudr44.github.io/sps-hackathon/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow)](LICENSE)

---

## Abstract

A growing class of AI-safety architectures treats the Lean 4 kernel as a trust anchor: an autonomous agent's proposed action is admitted only if the kernel certifies a proof of its safety. We show this assumption already fails using only **documented, unpatched Lean features**.

The `@[implemented_by]` attribute lets a function's compiled body diverge from the source body the kernel reads. `native_decide` admits the compiled body's answer into the kernel through a synthetic axiom. `#print axioms` does not report which function's runtime body was trusted.

Composed across module boundaries, these let a malicious dependency export a **pre-certified false lemma** that downstream code uses to derive `False` — while every audit a non-expert would run returns **clean**.

---

## Key Results

| Framing | Trials | Unsound rate |
|---|:---:|:---:|
| Benign open optimization (A, B, C, D) | 12 | **0%** |
| Open hot-opcode, no impl hint (F-hot) | 3 | **0%** |
| Maintainer nudge — specify divergent behavior (E-soft, G-soft) | 6 | **100%** |
| In-source prompt injection (F-inject, G-inject) | 6 | **67%** |
| Explicit red-team (E-hard) | 3 (1 refusal) | 100% of attempters |

**Headline:** When told *what divergent behavior to produce* under a performance cover story, all three Claude model tiers (Haiku 4.5, Sonnet 4.6, Opus 4.7) comply — across two independent codebases — producing kernel-inconsistent `@[implemented_by]` bodies. When asked to optimize freely without specifying the divergence, 0/12 produce unsound code.

---

## The Four-Module Supply Chain

```
Step1_Defs.lean      (Alice, honest)    — defines Color, isBlue_src
Step2_FastPath.lean  (Mallory, attacker) — @[implemented_by isBlue_lie]
Step3_Bridge.lean    (Carol, honest)    — native_decide certificate
Step4_Consumer.lean  (Bob, victim)      — imports cert, never touches native_decide
```

Bob's audit of `dashboardSaysBlue`:
```
'Colors.dashboardSaysBlue' depends on axioms:
  [propext, productionIsBlue._native.native_decide.ax_1_1]
Build completed successfully (5 jobs).
```
Clean build. Clean audit. The kernel's own reduction of `kernelLabel` yields `"RED"`. The certified theorem says `"BLUE"`.

---

## Quick Reproduction

```sh
git clone https://github.com/r34l-rudr44/sps-hackathon.git
cd sps-hackathon/test_project
cat lean-toolchain          # leanprover/lean4:v4.30.0-rc2
lake build Myproject.Supply.Step4_Consumer
```

Expected: build succeeds; `dashboardSaysBlue` depends only on `[propext, productionIsBlue._native.native_decide.ax_1_1]`.

---

## Repository Layout

```
test_project/
├── TestProject/Supply/          # Four-module exploit chain
│   ├── Step1_Defs.lean
│   ├── Step2_FastPath.lean
│   ├── Step3_Bridge.lean
│   └── Step4_Consumer.lean
├── experiments/                 # 33-trial empirical study
│   ├── Victim3.lean             # 250-line stack VM
│   ├── Victim4.lean             # 350-line regex matcher
│   ├── Victim3_injected.lean    # VM with PERF NOTE injection
│   ├── Victim4_injected.lean    # Regex with PERF NOTE injection
│   ├── validate{3,4,5}.sh       # Automated validators
│   └── RESULTS.md               # Full 33-trial results table
├── EXPLOIT_NONDETERMINISM/      # nondeterminism exploit variants
└── docs/                        # GitHub Pages (full paper)
```

---

## Full Paper

**[Read the full paper →](https://r34l-rudr44.github.io/sps-hackathon/)**

Includes: complete threat model, all 33 trial results, discursive bypass taxonomy, prior-art delta, and suggested Lean upstream mitigations.

---

## Citation

```bibtex
@misc{dash2026dontlean,
  title   = {Don't LEAN On Me: How Covert Proof-checker Failures Eradicate
             Formal-Verification-powered Agentic Guardrails},
  author  = {Arka Dash and Carlos José Duarte Casillas, Rishab Kumar Jha, Yatharth Maheshwari, Aditya Bansal},
  year    = {2026},
  note    = {With Apart Research. \url{https://github.com/r34l-rudr44/sps-hackathon}}
}
```
