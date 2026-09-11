/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
/-!

# Vectors in the causal future of the origin

## i. Overview

A vector `u` with `causallyFollows 0 u` is future-directed causal: time-like or light-like with a
nonnegative time component (`causallyFollows_zero_iff`). For two such vectors of Minkowski space
(signature `+---`), the Minkowski product dominates the product of the Minkowski norms,
`⟪u, v⟫ₘ ≥ √⟪u, u⟫ₘ √⟪v, v⟫ₘ` (reverse Cauchy-Schwarz inequality), and the Minkowski norm of the
sum dominates the sum of the norms, `√⟪u + v, u + v⟫ₘ ≥ √⟪u, u⟫ₘ + √⟪v, v⟫ₘ` (reverse triangle
inequality). The proofs reduce to the elementary inequality `√(a² - c²) √(b² - d²) ≤ a b - c d` for
`0 ≤ c ≤ a`, `0 ≤ d ≤ b`, applied to the time components and the Euclidean norms of the spatial
parts, together with the Euclidean Cauchy-Schwarz inequality.

## ii. Key results

- `causallyFollows_zero_iff`: `causallyFollows 0 u ↔ 0 ≤ ⟪u, u⟫ₘ ∧ 0 ≤ u⁰`;
  `causallyFollows_zero_sub`: `q - p` is in the causal future of `0` when `q` causally follows `p`.
- `norm_spatialPart_le_timeComponent`: `‖u_spatial‖ ≤ u⁰`.
- `sqrt_mul_sqrt_le_minkowskiProduct`: the reverse Cauchy-Schwarz inequality.
- `sqrt_add_sqrt_le_sqrt_add`: the reverse triangle inequality; `causallyFollows_zero_add`.

## iii. Table of contents

- A. The causal future of the origin
- B. The reverse Cauchy-Schwarz inequality
- C. The reverse triangle inequality

-/

@[expose] public section

namespace Lorentz

namespace Vector

open InnerProductSpace

/-!

## A. The causal future of the origin

-/

/-- A vector is in the causal future of the origin if and only if it is time-like or light-like
  (`0 ≤ ⟪u, u⟫ₘ`) with a nonnegative time component. -/
lemma causallyFollows_zero_iff {d : ℕ} {u : Vector d} :
    causallyFollows 0 u ↔ 0 ≤ ⟪u, u⟫ₘ ∧ 0 ≤ u.timeComponent := by
  simp only [causallyFollows, interiorFutureLightCone, futureLightConeBoundary, Set.mem_ofPred_eq,
    sub_zero, timeLike_iff_norm_sq_pos, lightLike_iff_norm_sq_zero]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1.le, h2.le⟩
    · exact ⟨h1.ge, h2⟩
  · rintro ⟨h1, h2⟩
    rcases h1.lt_or_eq with h1 | h1
    · left
      refine ⟨h1, lt_of_le_of_ne h2 fun h0 => ?_⟩
      have h := minkowskiProduct_self_le_timeComponent_sq u
      have h0' : u.timeComponent = 0 := h0.symm
      rw [h0'] at h
      norm_num at h
      linarith
    · right
      exact ⟨h1.symm, h2⟩

/-- The vector from `p` to `q` is in the causal future of the origin when `q` causally
  follows `p`. -/
lemma causallyFollows_zero_sub {d : ℕ} {p q : Vector d} (h : causallyFollows p q) :
    causallyFollows 0 (q - p) := by
  simpa only [causallyFollows, interiorFutureLightCone, futureLightConeBoundary, Set.mem_ofPred_eq,
    sub_zero] using h

/-!

## B. The reverse Cauchy-Schwarz inequality

-/

/-- For a vector in the causal future of the origin, the Euclidean norm of the spatial part is at
  most the time component. -/
lemma norm_spatialPart_le_timeComponent {d : ℕ} {u : Vector d} (hu : causallyFollows 0 u) :
    ‖u.spatialPart‖ ≤ u.timeComponent := by
  obtain ⟨h1, _⟩ := causallyFollows_zero_iff.mp hu
  rw [minkowskiProduct_self_eq_sq_sub] at h1
  nlinarith [norm_nonneg u.spatialPart]

/-- The reverse Cauchy-Schwarz inequality: for `u`, `v` in the causal future of the origin,
  `√⟪u, u⟫ₘ √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ`. -/
lemma sqrt_mul_sqrt_le_minkowskiProduct {d : ℕ} {u v : Vector d} (hu : causallyFollows 0 u)
    (hv : causallyFollows 0 v) : √⟪u, u⟫ₘ * √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ := by
  have hu' := norm_spatialPart_le_timeComponent hu
  have hv' := norm_spatialPart_le_timeComponent hv
  rw [minkowskiProduct_self_eq_sq_sub u, minkowskiProduct_self_eq_sq_sub v,
    minkowskiProduct_eq_timeComponent_spatialPart u v]
  have hcs := real_inner_le_norm u.spatialPart v.spatialPart
  set a := u.timeComponent
  set c := ‖u.spatialPart‖
  set b := v.timeComponent
  set e := ‖v.spatialPart‖
  have hc0 : 0 ≤ c := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  have helem : √(a ^ 2 - c ^ 2) * √(b ^ 2 - e ^ 2) ≤ a * b - c * e := by
    -- the elementary inequality `√(a² - c²) √(b² - e²) ≤ a b - c e` for `0 ≤ c ≤ a`, `0 ≤ e ≤ b`:
    -- indeed `(a b - c e)² - (a² - c²)(b² - e²) = (a e - b c)²`
    have h1 : 0 ≤ a ^ 2 - c ^ 2 := by nlinarith
    have h2 : 0 ≤ a * b - c * e := by nlinarith
    calc √(a ^ 2 - c ^ 2) * √(b ^ 2 - e ^ 2) = √((a ^ 2 - c ^ 2) * (b ^ 2 - e ^ 2)) :=
          (Real.sqrt_mul h1 _).symm
      _ ≤ √((a * b - c * e) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a * e - b * c)])
      _ = a * b - c * e := Real.sqrt_sq h2
  linarith

/-!

## C. The reverse triangle inequality

-/

/-- The reverse triangle inequality: for `u`, `v` in the causal future of the origin,
  `√⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ`. -/
lemma sqrt_add_sqrt_le_sqrt_add {d : ℕ} {u v : Vector d} (hu : causallyFollows 0 u)
    (hv : causallyFollows 0 v) : √⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ := by
  have hcs := sqrt_mul_sqrt_le_minkowskiProduct hu hv
  have hu1 := (causallyFollows_zero_iff.mp hu).1
  have hv1 := (causallyFollows_zero_iff.mp hv).1
  have hsum : (√⟪u, u⟫ₘ + √⟪v, v⟫ₘ) ^ 2 ≤ ⟪u + v, u + v⟫ₘ := by
    rw [minkowskiProduct_add_self, add_sq, Real.sq_sqrt hu1, Real.sq_sqrt hv1]
    linarith
  exact Real.le_sqrt_of_sq_le hsum

/-- The sum of two vectors in the causal future of the origin is in the causal future of the
  origin. -/
lemma causallyFollows_zero_add {d : ℕ} {u v : Vector d} (hu : causallyFollows 0 u)
    (hv : causallyFollows 0 v) : causallyFollows 0 (u + v) := by
  obtain ⟨hu1, hu2⟩ := causallyFollows_zero_iff.mp hu
  obtain ⟨hv1, hv2⟩ := causallyFollows_zero_iff.mp hv
  refine causallyFollows_zero_iff.mpr ⟨?_, ?_⟩
  · have hcs := sqrt_mul_sqrt_le_minkowskiProduct hu hv
    have hsq : 0 ≤ (√⟪u, u⟫ₘ + √⟪v, v⟫ₘ) ^ 2 := sq_nonneg _
    rw [add_sq, Real.sq_sqrt hu1, Real.sq_sqrt hv1] at hsq
    rw [minkowskiProduct_add_self]
    linarith
  · show 0 ≤ (u + v) (Sum.inl 0)
    rw [apply_add]
    exact add_nonneg hu2 hv2

end Vector

end Lorentz
