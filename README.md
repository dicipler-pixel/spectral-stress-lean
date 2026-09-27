<div align="center">

# Spectral Stress on a Conservative Matrix Field — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/spectral-stress-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/spectral-stress-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-20-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21825872-blue)](https://doi.org/10.5281/zenodo.21825872)

Jeromie Beasley

</div>

---

## The idea in one line

A flat connection can carry a curved eigenline bundle. The curvature of each band is a sum of
antisymmetric pair terms, so the bands' curvatures sum to zero exactly, and once the two
transport directions are tied by one operator relation, every pair term factorises. The
amplitude `A = −5√2/16`, the vanishing middle band and the 4:1 ratio then follow as exact
arithmetic in `ℚ(√2)`.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Prop. 1 | The pair term is antisymmetric, so `Σ_b F_b = 0` exactly | `pairTerm_antisymm`, `sum_rule` |
| Sec. 2.2 | The ratio `ρ_bc` and the two-cycle `β_bc β_cb` are gauge-invariant | `ratio_gauge`, `twocycle_gauge` |
| Theorem 2 | `t(b,c) = (ρ_b − ρ_c) β_bc β_cb` | `factorisation` |
| Corollary 1 | A band-independent `ρ` makes every pair term vanish | `vanishing` |
| Prop. 2 | Pair terms `−√2/16`, `−√2/4`, `−√2/4`; `A = −5√2/16`, `F_mid = 0`, `F_rec = −A`; the 4:1 ratio | `t_dom_rec`, `t_dom_mid`, `t_mid_rec`, `amplitude`, `pair_ratio` |
| Sec. 2.1 | `17 ± 12√2 = (1 ± √2)⁴`; the squared gaps; the numerators over the gaps; `544² − 2·384² = 1024` | `limiting_spectrum`, `squared_gaps`, `numerators_over_gaps`, `norm_identity` |
| Sec. 2.2 | `ρ_dom, ρ_rec` are roots of `x² + 16x + 32`, and `g = ρ + 1` of `x² + 14x + 17`; the two-cycles are conjugate with sum `−1/8` and product `−1/256` | `rho_roots`, `g_roots`, `twocycles_conjugate` |
| Theorem 3 | A gap of `δ^{1/2}` and curvature of `gap^{−3}` give `δ^{−3/2}` | `ep_rate` |

The file is [`SpectralStress/Basic.lean`](SpectralStress/Basic.lean). What is not proved is in
[`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*Spectral Stress on a Conservative Matrix Field*, Jeromie Beasley. DOI
[10.5281/zenodo.21825872](https://doi.org/10.5281/zenodo.21825872) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
