/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
/-!

# The reverse Cauchy-Schwarz and reverse triangle inequalities

## i. Overview

For two future-directed causal vectors `u`, `v` of Minkowski space (signature `+---`), the
Minkowski product dominates the product of the Minkowski norms, `⟪u, v⟫ₘ ≥ √⟪u, u⟫ₘ √⟪v, v⟫ₘ`
(reverse Cauchy-Schwarz inequality), and the Minkowski norm of the sum dominates the sum of the
norms, `√⟪u + v, u + v⟫ₘ ≥ √⟪u, u⟫ₘ + √⟪v, v⟫ₘ` (reverse triangle inequality). The proof reduces to
the elementary inequality `√(a² - c²) √(b² - d²) ≤ a b - c d` for `0 ≤ c ≤ a`, `0 ≤ d ≤ b`, applied
to the time components and the Euclidean norms of the spatial parts, together with the Euclidean
Cauchy-Schwarz inequality.

## ii. Key results

- `IsFutureCausal`: `0 ≤ ⟪u, u⟫ₘ` and `0 ≤ u⁰`; `isFutureCausal_of_causallyFollows`.
- `sqrt_mul_sqrt_le`: the elementary inequality.
- `norm_spatialPart_le_timeComponent`: `‖u_spatial‖ ≤ u⁰` for `u` future causal.
- `sqrt_mul_sqrt_le_minkowskiProduct`: the reverse Cauchy-Schwarz inequality.
- `sqrt_add_sqrt_le_sqrt_add`: the reverse triangle inequality; `isFutureCausal_add`.
- `minkowskiProduct_eq_iff`: equality in the reverse Cauchy-Schwarz inequality holds if and only
  if the two vectors are proportional (with a nonnegative factor).
- `sqrt_add_eq_iff`: equality in the reverse triangle inequality holds if and only if equality
  holds in the reverse Cauchy-Schwarz inequality.

## iii. Table of contents

- A. Future-directed causal vectors
- B. The elementary inequality
- C. The reverse Cauchy-Schwarz inequality
- D. The reverse triangle inequality
- E. The equality cases

-/

@[expose] public section

namespace Lorentz

namespace Vector

open InnerProductSpace

/-!

## A. Future-directed causal vectors

-/

/-- A vector is future-directed causal if it is time-like or light-like (`0 ≤ ⟪u, u⟫ₘ`) with a
  nonnegative time component. -/
def IsFutureCausal {d : ℕ} (u : Vector d) : Prop := 0 ≤ ⟪u, u⟫ₘ ∧ 0 ≤ u.timeComponent

/-- The vector from `p` to `q` is future-directed causal when `q` causally follows `p`. -/
lemma isFutureCausal_of_causallyFollows {d : ℕ} {p q : Vector d} (h : causallyFollows p q) :
    IsFutureCausal (q - p) := by
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := h
    exact ⟨((timeLike_iff_norm_sq_pos _).mp h1).le, h2.le⟩
  · obtain ⟨h1, h2⟩ := h
    exact ⟨((lightLike_iff_norm_sq_zero _).mp h1).ge, h2⟩

/-!

## B. The elementary inequality

-/

/-- For `0 ≤ c ≤ a` and `0 ≤ d ≤ b`, `√(a² - c²) √(b² - d²) ≤ a b - c d`: indeed
  `(a b - c d)² - (a² - c²)(b² - d²) = (a d - b c)²`. -/
lemma sqrt_mul_sqrt_le {a b c d : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) (hd : 0 ≤ d) (hdb : d ≤ b) :
    √(a ^ 2 - c ^ 2) * √(b ^ 2 - d ^ 2) ≤ a * b - c * d := by
  have h1 : 0 ≤ a ^ 2 - c ^ 2 := by nlinarith
  have h2 : 0 ≤ a * b - c * d := by nlinarith
  calc √(a ^ 2 - c ^ 2) * √(b ^ 2 - d ^ 2) = √((a ^ 2 - c ^ 2) * (b ^ 2 - d ^ 2)) :=
        (Real.sqrt_mul h1 _).symm
    _ ≤ √((a * b - c * d) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a * d - b * c)])
    _ = a * b - c * d := Real.sqrt_sq h2

/-!

## C. The reverse Cauchy-Schwarz inequality

-/

/-- `⟪u, u⟫ₘ = (u⁰)² - ‖u_spatial‖²`. -/
lemma minkowskiProduct_self_eq_sq_sub {d : ℕ} (u : Vector d) :
    ⟪u, u⟫ₘ = u.timeComponent ^ 2 - ‖u.spatialPart‖ ^ 2 := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart, Real.norm_eq_abs, sq_abs]

/-- For a future-directed causal vector, the Euclidean norm of the spatial part is at most the
  time component. -/
lemma norm_spatialPart_le_timeComponent {d : ℕ} {u : Vector d} (hu : IsFutureCausal u) :
    ‖u.spatialPart‖ ≤ u.timeComponent := by
  obtain ⟨h1, h2⟩ := hu
  rw [minkowskiProduct_self_eq_sq_sub] at h1
  nlinarith [norm_nonneg u.spatialPart]

/-- The reverse Cauchy-Schwarz inequality: for future-directed causal `u`, `v`,
  `√⟪u, u⟫ₘ √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ`. -/
lemma sqrt_mul_sqrt_le_minkowskiProduct {d : ℕ} {u v : Vector d} (hu : IsFutureCausal u)
    (hv : IsFutureCausal v) : √⟪u, u⟫ₘ * √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ := by
  have hu' := norm_spatialPart_le_timeComponent hu
  have hv' := norm_spatialPart_le_timeComponent hv
  rw [minkowskiProduct_self_eq_sq_sub u, minkowskiProduct_self_eq_sq_sub v,
    minkowskiProduct_eq_timeComponent_spatialPart u v]
  have hcs := real_inner_le_norm u.spatialPart v.spatialPart
  have := sqrt_mul_sqrt_le (norm_nonneg u.spatialPart) hu' (norm_nonneg v.spatialPart) hv'
  linarith

/-!

## D. The reverse triangle inequality

-/

/-- `⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 ⟪u, v⟫ₘ + ⟪v, v⟫ₘ`. -/
lemma minkowskiProduct_add_self {d : ℕ} (u v : Vector d) :
    ⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
  simp only [map_add, add_apply]
  rw [minkowskiProduct_symm v u]
  ring

/-- The reverse triangle inequality: for future-directed causal `u`, `v`,
  `√⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ`. -/
lemma sqrt_add_sqrt_le_sqrt_add {d : ℕ} {u v : Vector d} (hu : IsFutureCausal u)
    (hv : IsFutureCausal v) : √⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ := by
  have hcs := sqrt_mul_sqrt_le_minkowskiProduct hu hv
  have hsum : (√⟪u, u⟫ₘ + √⟪v, v⟫ₘ) ^ 2 ≤ ⟪u + v, u + v⟫ₘ := by
    rw [minkowskiProduct_add_self, add_sq, Real.sq_sqrt hu.1, Real.sq_sqrt hv.1]
    linarith
  exact Real.le_sqrt_of_sq_le hsum

/-- The sum of two future-directed causal vectors is future-directed causal. -/
lemma isFutureCausal_add {d : ℕ} {u v : Vector d} (hu : IsFutureCausal u) (hv : IsFutureCausal v) :
    IsFutureCausal (u + v) := by
  refine ⟨?_, ?_⟩
  · have hcs := sqrt_mul_sqrt_le_minkowskiProduct hu hv
    have hsq : 0 ≤ (√⟪u, u⟫ₘ + √⟪v, v⟫ₘ) ^ 2 := sq_nonneg _
    rw [add_sq, Real.sq_sqrt hu.1, Real.sq_sqrt hv.1] at hsq
    rw [minkowskiProduct_add_self]
    linarith
  · show 0 ≤ (u + v) (Sum.inl 0)
    rw [apply_add]
    exact add_nonneg hu.2 hv.2

/-!

## E. The equality cases

-/

/-- A vector with zero time component and zero spatial part is zero. -/
lemma eq_zero_of_timeComponent_of_spatialPart {d : ℕ} {u : Vector d} (h0 : u.timeComponent = 0)
    (hs : u.spatialPart = 0) : u = 0 := by
  refine ext_of_apply fun i => ?_
  rcases i with i | i
  · fin_cases i
    exact h0
  · have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hs
    simpa [spatialPart_apply_eq_toCoord] using this

/-- The spatial components of a vector whose spatial part has zero norm vanish. -/
lemma apply_inr_eq_zero_of_norm_spatialPart {d : ℕ} {u : Vector d} (h : ‖u.spatialPart‖ = 0)
    (i : Fin d) : u (Sum.inr i) = 0 := by
  have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) (norm_eq_zero.mp h)
  simpa [spatialPart_apply_eq_toCoord] using this

/-- `⟪μ • u, μ • u⟫ₘ = μ² ⟪u, u⟫ₘ`. -/
lemma minkowskiProduct_smul_self {d : ℕ} (μ : ℝ) (u : Vector d) :
    ⟪μ • u, μ • u⟫ₘ = μ ^ 2 * ⟪u, u⟫ₘ := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- `√⟪μ • u, μ • u⟫ₘ = μ √⟪u, u⟫ₘ` for `μ ≥ 0`. -/
lemma sqrt_minkowskiProduct_smul_self {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (u : Vector d) :
    √⟪μ • u, μ • u⟫ₘ = μ * √⟪u, u⟫ₘ := by
  rw [minkowskiProduct_smul_self, Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ]

/-- Equality in the reverse Cauchy-Schwarz inequality: for future-directed causal `u`, `v`,
  `⟪u, v⟫ₘ = √⟪u, u⟫ₘ √⟪v, v⟫ₘ` if and only if one of the vectors is a nonnegative multiple of
  the other. -/
lemma minkowskiProduct_eq_iff {d : ℕ} {u v : Vector d} (hu : IsFutureCausal u)
    (hv : IsFutureCausal v) :
    ⟪u, v⟫ₘ = √⟪u, u⟫ₘ * √⟪v, v⟫ₘ ↔ ∃ μ : ℝ, 0 ≤ μ ∧ (v = μ • u ∨ u = μ • v) := by
  constructor
  · intro heq
    have hu' := norm_spatialPart_le_timeComponent hu
    have hv' := norm_spatialPart_le_timeComponent hv
    have hcs := real_inner_le_norm u.spatialPart v.spatialPart
    have helem := sqrt_mul_sqrt_le (norm_nonneg u.spatialPart) hu' (norm_nonneg v.spatialPart) hv'
    rw [minkowskiProduct_self_eq_sq_sub u, minkowskiProduct_self_eq_sq_sub v,
      minkowskiProduct_eq_timeComponent_spatialPart u v] at heq
    set a := u.timeComponent with ha
    set c := ‖u.spatialPart‖ with hc
    set b := v.timeComponent with hb
    set e := ‖v.spatialPart‖ with he
    have hinner : ⟪u.spatialPart, v.spatialPart⟫_ℝ = c * e := by linarith
    have hsq : √(a ^ 2 - c ^ 2) * √(b ^ 2 - e ^ 2) = a * b - c * e := by linarith
    have hc0 : 0 ≤ c := norm_nonneg _
    have he0 : 0 ≤ e := norm_nonneg _
    have h1 : (a ^ 2 - c ^ 2) * (b ^ 2 - e ^ 2) = (a * b - c * e) ^ 2 := by
      have := congrArg (· ^ 2) hsq
      rw [mul_pow, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)] at this
      exact this
    have hadbc : a * e - b * c = 0 := by
      have : (a * e - b * c) ^ 2 = 0 := by linear_combination (-1 : ℝ) * h1
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    have hpar := inner_eq_norm_mul_iff_real.mp hinner
    have hcomp : ∀ i, e * u (Sum.inr i) = c * v (Sum.inr i) := fun i => by
      have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hpar
      simpa [spatialPart_apply_eq_toCoord] using this
    by_cases ha0 : a = 0
    · have hcz : c = 0 := le_antisymm (ha0 ▸ hu') hc0
      have hu0 : u = 0 :=
        eq_zero_of_timeComponent_of_spatialPart ha0 (norm_eq_zero.mp hcz)
      exact ⟨0, le_rfl, Or.inr (by rw [hu0, zero_smul])⟩
    · have hapos : 0 < a := lt_of_le_of_ne hu.2 (Ne.symm ha0)
      refine ⟨b / a, div_nonneg hv.2 hapos.le, Or.inl ?_⟩
      refine ext_of_apply fun i => ?_
      rw [apply_smul]
      rcases i with i | i
      · fin_cases i
        show b = b / a * a
        field_simp
      · have key : a * v (Sum.inr i) = b * u (Sum.inr i) := by
          by_cases hcz : c = 0
          · have hez : e = 0 := by
              have : a * e = 0 := by rw [hcz] at hadbc; linarith
              exact (mul_eq_zero.mp this).resolve_left ha0
            rw [apply_inr_eq_zero_of_norm_spatialPart hcz,
              apply_inr_eq_zero_of_norm_spatialPart hez]
            ring
          · have h := hcomp i
            apply mul_left_cancel₀ hcz
            linear_combination (-a) * h + u (Sum.inr i) * hadbc
        show v (Sum.inr i) = b / a * u (Sum.inr i)
        field_simp
        linarith
  · rintro ⟨μ, hμ, h | h⟩
    · subst h
      rw [sqrt_minkowskiProduct_smul_self hμ u, map_smul, smul_eq_mul]
      have := Real.mul_self_sqrt hu.1
      linear_combination μ * this.symm
    · subst h
      rw [sqrt_minkowskiProduct_smul_self hμ v, map_smul, smul_apply, smul_eq_mul]
      have := Real.mul_self_sqrt hv.1
      linear_combination μ * this.symm

/-- Equality in the reverse triangle inequality holds if and only if equality holds in the
  reverse Cauchy-Schwarz inequality. -/
lemma sqrt_add_eq_iff {d : ℕ} {u v : Vector d} (hu : IsFutureCausal u) (hv : IsFutureCausal v) :
    √⟪u + v, u + v⟫ₘ = √⟪u, u⟫ₘ + √⟪v, v⟫ₘ ↔ ⟪u, v⟫ₘ = √⟪u, u⟫ₘ * √⟪v, v⟫ₘ := by
  have hsum := minkowskiProduct_add_self u v
  have hnn := (isFutureCausal_add hu hv).1
  constructor
  · intro h
    have h2 := congrArg (· ^ 2) h
    rw [Real.sq_sqrt hnn, add_sq, Real.sq_sqrt hu.1, Real.sq_sqrt hv.1] at h2
    linarith
  · intro h
    rw [Real.sqrt_eq_iff_mul_self_eq hnn (by positivity), hsum, h]
    have := Real.mul_self_sqrt hu.1
    have := Real.mul_self_sqrt hv.1
    ring_nf
    nlinarith [Real.mul_self_sqrt hu.1, Real.mul_self_sqrt hv.1]

end Vector

end Lorentz
