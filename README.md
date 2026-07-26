# Formalising the supersaturation theorem in Lean

[![Lean Action CI](https://github.com/mitchell-horner/Supersaturation/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mitchell-horner/Supersaturation/actions/workflows/lean_action_ci.yml)

This repository contains a formalisation of the supersaturation theorem in [Lean](https://lean-lang.org/). The statements of the results are as follows:

**The supersaturation theorem**

Suppose $\varepsilon > 0$ is a positive real number, and $G,H$ are simple graphs. If the number of vertices $v(G)$ is sufficiently large and $G$ has at least $(\pi(H) + \varepsilon) \binom{v(G)}{2}$ many edges, then $G$ contains at least $\delta \cdot v(G) ^ {v(H)}$ labelled copies of $H$, where $\delta = \delta(H, \varepsilon)$ is an explicit constant.

```lean
theorem eventually_labelledCopyCount_ge_of_card_edgeFinset {ε : ℝ} (hε_pos : 0 < ε) :
  ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
    #G.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 →
      G.labelledCopyCount H ≥ supersaturationConst H ε * n ^ card W
```

## Upstreaming to mathlib

The progress towards upstreaming these results to [mathlib](https://github.com/leanprover-community/mathlib4) is as follows:

- [ ] The supersaturation theorem

## Future work

Future work could include:

- Wenger's theorem
- The Bondy-Simonovits theorem
