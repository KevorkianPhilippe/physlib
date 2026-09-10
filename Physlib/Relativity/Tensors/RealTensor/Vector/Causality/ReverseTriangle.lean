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

## iii. Table of contents

- A. Future-directed causal vectors
- B. The elementary inequality
- C. The reverse Cauchy-Schwarz inequality
- D. The reverse triangle inequality

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
