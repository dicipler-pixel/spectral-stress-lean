/-
Spectral Stress on a Conservative Matrix Field (Jeromie Beasley, DOI 10.5281/zenodo.21825872):
the exact algebra.

For simple eigenvalues `λ_b` with biorthogonal frames, write `a_bc = ⟨L_b|∂ₙT|R_c⟩`,
`k_bc = ⟨L_b|∂ₖT|R_c⟩`, and let the single pair term of Proposition 1 be
`t(b,c) = (a_bc k_cb − k_bc a_cb)/(λ_b − λ_c)²`, so that `F_b = Σ_{c ≠ b} t(b,c)`.

* Sum rule: `t(c,b) = −t(b,c)`, hence `Σ_b F_b = 0` exactly.
* Gauge: under `R_c ↦ γ_c R_c`, `L_b ↦ L_b/γ_b`, every element picks up `γ_c/γ_b`; the ratio
  `ρ_bc = a_bc/k_bc` and the two-cycle `β_bc β_cb` are invariant.
* Theorem 2 (factorisation): if `a_bc = ρ_c k_bc` then `t(b,c) = (ρ_b − ρ_c) β_bc β_cb` with
  `β_bc = k_bc/(λ_b − λ_c)`; Corollary 1 (vanishing): a band-independent `ρ` gives `F_b = 0`.
* The amplitude: with `ρ_dom = −4(2+√2)`, `ρ_rec = −4(2−√2)`, `ρ_mid = 0` and the two-cycles
  `1/128`, `(√2−1)/16`, `−(√2+1)/16`, the pair terms are `−√2/16`, `−√2/4`, `−√2/4`, so
  `A = F_dom = −5√2/16`, `F_mid = 0` and `F_rec = −A`.
* The limiting spectrum `17 ± 12√2 = (1 ± √2)⁴` and 1, its squared gaps, the numerators, and the
  norm identity `544² − 2·384² = 1024`.
* `ρ_dom, ρ_rec` are the roots of `x² + 16x + 32`; the two-cycles are conjugate with sum `−1/8`
  and product `−1/256`.
* Theorem 3's rate: a gap `∼ δ^{1/2}` and curvature `∼ gap^{−3}` give `δ^{−3/2}`.
-/
import Mathlib

namespace SpectralStress

open Real

/-! ## Proposition 1: the pair term and the sum rule -/

/-- The single pair term of Proposition 1. -/
noncomputable def pairTerm {m : ℕ} (a k : Fin m → Fin m → ℝ) (lam : Fin m → ℝ) (b c : Fin m) :
    ℝ :=
  (a b c * k c b - k b c * a c b) / (lam b - lam c) ^ 2

/-- The pair term is antisymmetric. -/
theorem pairTerm_antisymm {m : ℕ} (a k : Fin m → Fin m → ℝ) (lam : Fin m → ℝ) (b c : Fin m) :
    pairTerm a k lam c b = -pairTerm a k lam b c := by
  unfold pairTerm
  rw [show (lam c - lam b) ^ 2 = (lam b - lam c) ^ 2 by ring, ← neg_div]
  ring_nf

/-- The band curvature `F_b = Σ_{c ≠ b} t(b,c)`. -/
noncomputable def curv {m : ℕ} (a k : Fin m → Fin m → ℝ) (lam : Fin m → ℝ) (b : Fin m) : ℝ :=
  ∑ c ∈ Finset.univ.erase b, pairTerm a k lam b c

/-- **The sum rule.** `Σ_b F_b = 0` exactly, by antisymmetry. -/
theorem sum_rule {m : ℕ} (a k : Fin m → Fin m → ℝ) (lam : Fin m → ℝ) :
    ∑ b, curv a k lam b = 0 := by
  unfold curv
  have hdiag : ∀ b, pairTerm a k lam b b = 0 := fun b => by simp [pairTerm]
  have h : ∀ b, ∑ c ∈ Finset.univ.erase b, pairTerm a k lam b c = ∑ c, pairTerm a k lam b c := by
    intro b
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), hdiag, zero_add]
  simp only [h]
  have hs : ∑ b, ∑ c, pairTerm a k lam b c = ∑ b, ∑ c, pairTerm a k lam c b :=
    Finset.sum_comm
  have hn : ∑ b, ∑ c, pairTerm a k lam c b = -∑ b, ∑ c, pairTerm a k lam b c := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => pairTerm_antisymm a k lam b c
  linarith

/-! ## Gauge invariance -/

/-- **Gauge.** Rescaling `R_c ↦ γ_c R_c`, `L_b ↦ L_b/γ_b` multiplies both directions' elements by
`γ_c/γ_b`, so the ratio `ρ_bc` is unchanged. -/
theorem ratio_gauge (x y γb γc : ℝ) (hb : γb ≠ 0) (hc : γc ≠ 0) :
    (γc / γb * x) / (γc / γb * y) = x / y := by
  rw [mul_div_mul_left _ _ (div_ne_zero hc hb)]

/-- **Gauge.** The two-cycle `β_bc β_cb` is unchanged. -/
theorem twocycle_gauge (x y γb γc : ℝ) (hb : γb ≠ 0) (hc : γc ≠ 0) :
    (γc / γb * x) * (γb / γc * y) = x * y := by
  field_simp

/-! ## Theorem 2 and Corollary 1 -/

/-- **Theorem 2 (factorisation).** If `a_bc = ρ_c k_bc` and `a_cb = ρ_b k_cb`, then
`t(b,c) = (ρ_b − ρ_c) β_bc β_cb` with `β_bc = k_bc/(λ_b − λ_c)`. -/
theorem factorisation (kbc kcb lb lc ρb ρc : ℝ) (h : lb ≠ lc) :
    ((ρc * kbc) * kcb - kbc * (ρb * kcb)) / (lb - lc) ^ 2 =
      (ρb - ρc) * (kbc / (lb - lc)) * (kcb / (lc - lb)) := by
  have h1 : lb - lc ≠ 0 := sub_ne_zero.mpr h
  have h2 : lc - lb ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp
  ring

/-- **Corollary 1 (vanishing).** If `ρ` is the same on every band the pair term vanishes. -/
theorem vanishing (kbc kcb lb lc ρ : ℝ) :
    ((ρ * kbc) * kcb - kbc * (ρ * kcb)) / (lb - lc) ^ 2 = 0 := by
  ring

/-! ## The amplitude `A = −5√2/16` -/

theorem sqrt2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

noncomputable def ρdom : ℝ := -4 * (2 + √2)
noncomputable def ρrec : ℝ := -4 * (2 - √2)
def ρmid : ℝ := 0

/-- The pair term `(dom, rec)`: `(ρ_dom − ρ_rec)/128 = −√2/16`. -/
theorem t_dom_rec : (ρdom - ρrec) * (1 / 128) = -√2 / 16 := by
  unfold ρdom ρrec; ring

/-- The pair term `(dom, mid)`: `(ρ_dom − 0)(√2 − 1)/16 = −√2/4`. -/
theorem t_dom_mid : (ρdom - ρmid) * ((√2 - 1) / 16) = -√2 / 4 := by
  unfold ρdom ρmid; nlinarith [sqrt2_sq]

/-- The pair term `(mid, rec)`: `(0 − ρ_rec)(−(√2 + 1)/16) = −√2/4`. -/
theorem t_mid_rec : (ρmid - ρrec) * (-(√2 + 1) / 16) = -√2 / 4 := by
  unfold ρrec ρmid; nlinarith [sqrt2_sq]

/-- **Proposition 2.** `A = F_dom = t(dom,mid) + t(dom,rec) = −5√2/16`; `F_mid = 0`;
`F_rec = −A`: the leading curvature is a pure dominant–recessive exchange. -/
theorem amplitude :
    (ρdom - ρmid) * ((√2 - 1) / 16) + (ρdom - ρrec) * (1 / 128) = -5 * √2 / 16 ∧
    -((ρdom - ρmid) * ((√2 - 1) / 16)) + (ρmid - ρrec) * (-(√2 + 1) / 16) = 0 ∧
    -((ρdom - ρrec) * (1 / 128)) - (ρmid - ρrec) * (-(√2 + 1) / 16) = 5 * √2 / 16 := by
  rw [t_dom_mid, t_dom_rec, t_mid_rec]
  refine ⟨by ring, by ring, by ring⟩

/-- The 4:1 pair ratio `(√2/4)/(√2/16) = 4`. -/
theorem pair_ratio : (√2 / 4) / (√2 / 16) = 4 := by
  have : (√2 : ℝ) ≠ 0 := by positivity
  field_simp; norm_num

/-! ## The limiting spectrum -/

/-- `17 + 12√2 = (1 + √2)⁴` and `17 − 12√2 = (1 − √2)⁴`. -/
theorem limiting_spectrum : (1 + √2) ^ 4 = 17 + 12 * √2 ∧ (1 - √2) ^ 4 = 17 - 12 * √2 := by
  have h4 : (√2 : ℝ) ^ 4 = 4 := by rw [show 4 = 2 * 2 by rfl, pow_mul, sqrt2_sq]; norm_num
  have h3 : (√2 : ℝ) ^ 3 = 2 * √2 := by rw [pow_succ, sqrt2_sq]
  constructor <;> ring_nf <;> rw [h4, h3, sqrt2_sq] <;> ring

/-- The squared gaps of the limiting spectrum `17 + 12√2, 1, 17 − 12√2`. -/
theorem squared_gaps :
    (17 + 12 * √2 - 1) ^ 2 = 544 + 384 * √2 ∧ (1 - (17 - 12 * √2)) ^ 2 = 544 - 384 * √2 ∧
      (17 + 12 * √2 - (17 - 12 * √2)) ^ 2 = 1152 := by
  refine ⟨by nlinarith [sqrt2_sq], by nlinarith [sqrt2_sq], by nlinarith [sqrt2_sq]⟩

/-- The norm identity that makes the quotients rational. -/
theorem norm_identity : (544 : ℤ) ^ 2 - 2 * 384 ^ 2 = 1024 := by norm_num

/-- **Sec. 2.1.** Each numerator over its squared gap: `−(192+136√2)/(544+384√2) = −√2/4`,
`(192−136√2)/(544−384√2) = −√2/4`, `−72√2/1152 = −√2/16`. -/
theorem numerators_over_gaps :
    -(192 + 136 * √2) / (544 + 384 * √2) = -√2 / 4 ∧
      (192 - 136 * √2) / (544 - 384 * √2) = -√2 / 4 ∧ -72 * √2 / 1152 = -√2 / 16 := by
  have hs := sqrt2_sq
  have hlt : √2 < 17 / 12 := by nlinarith [Real.sqrt_nonneg 2]
  have hp : 0 < 544 + 384 * √2 := by positivity
  have hm : 0 < 544 - 384 * √2 := by linarith
  refine ⟨?_, ?_, by ring⟩
  · rw [div_eq_div_iff hp.ne' (by norm_num)]; nlinarith
  · rw [div_eq_div_iff hm.ne' (by norm_num)]; nlinarith

/-- `ρ_dom` and `ρ_rec` are the roots of `x² + 16x + 32`. -/
theorem rho_roots : ρdom ^ 2 + 16 * ρdom + 32 = 0 ∧ ρrec ^ 2 + 16 * ρrec + 32 = 0 := by
  unfold ρdom ρrec
  constructor <;> nlinarith [sqrt2_sq]

/-- `g = ρ + 1` are the roots of `x² + 14x + 17`. -/
theorem g_roots : (ρdom + 1) ^ 2 + 14 * (ρdom + 1) + 17 = 0 ∧
    (ρrec + 1) ^ 2 + 14 * (ρrec + 1) + 17 = 0 := by
  obtain ⟨h1, h2⟩ := rho_roots
  constructor <;> nlinarith

/-- The two-cycles `(√2−1)/16` and `−(√2+1)/16` are conjugate, with sum `−1/8` and product
`−1/256`. -/
theorem twocycles_conjugate :
    (√2 - 1) / 16 + -(√2 + 1) / 16 = -1 / 8 ∧ (√2 - 1) / 16 * (-(√2 + 1) / 16) = -1 / 256 := by
  constructor
  · ring
  · nlinarith [sqrt2_sq]

/-! ## Theorem 3: the rate at the exceptional point -/

/-- **Theorem 3.** A gap `δ^{1/2}` and a curvature `gap^{−3}` give `δ^{−3/2}`. -/
theorem ep_rate (δ : ℝ) (hδ : 0 < δ) : (δ ^ (1 / 2 : ℝ)) ^ (-3 : ℝ) = δ ^ (-3 / 2 : ℝ) := by
  rw [← Real.rpow_mul hδ.le]
  norm_num

end SpectralStress
