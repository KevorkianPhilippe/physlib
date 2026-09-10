/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Philippe Kevorkian
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-!

# Exact solutions of the Friedmann equations

## i. Overview

This file collects the standard closed-form solutions of the Friedmann equations
(`FirstOrderFriedmann` and `SecondOrderFriedmann` of `Physlib.Cosmology.FLRW.Basic`) and
proves that they solve them: the de Sitter solution and the spatially flat power-law
solutions (radiation-dominated and Einstein-de Sitter) here, the Milne model and the
Einstein static universe being still TODO items.

Each solution is a scale factor `a : Time → ℝ` given by an explicit function of the time
coordinate `t.val`. Its time derivative `∂ₜ a` is computed through the bridge
`deriv_comp_toRealCLE_of_hasDerivAt` from Mathlib's `HasDerivAt` on `ℝ`.

## ii. Key results

- `deSitterScaleFactor`: `a(t) = a₀ exp(σ √(Λ/3) c t)` with `σ = ±1`.
- `deSitterScaleFactor_firstOrderFriedmann`, `deSitterScaleFactor_secondOrderFriedmann`:
  it solves both Friedmann equations with `ρ = 0`, `p = 0`, `k = 0` and `Λ > 0`.
- `hubbleConstant_deSitterScaleFactor`: its Hubble parameter is the constant `σ √(Λ/3) c`
  (for any `σ`, `Λ`, `c`).
- `decelerationParameter_deSitterScaleFactor`: its deceleration parameter is `q = -1`.
- `powerLawScaleFactor`: `a(t) = (t / t₀) ^ n`, with Hubble parameter `n / t`
  (`hubbleConstant_powerLawScaleFactor`) and deceleration parameter `(1 - n) / n`
  (`decelerationParameter_powerLawScaleFactor`) for `t > 0`.
- `radiationScaleFactor_firstOrderFriedmann`, `radiationScaleFactor_secondOrderFriedmann`:
  `a = (t / t₀) ^ (1/2)` solves the flat (`k = 0`, `Λ = 0`) Friedmann equations with the
  density `ρ = 3 / (32 π G t²)` and the radiation pressure `p = ρ c² / 3`; `q = 1` and
  `H(t₀) = 1 / (2 t₀)`.
- `einsteinDeSitterScaleFactor_firstOrderFriedmann`,
  `einsteinDeSitterScaleFactor_secondOrderFriedmann`: `a = (t / t₀) ^ (2/3)` solves the flat
  Friedmann equations with the dust density `ρ = 1 / (6 π G t²)` and `p = 0`; `q = 1 / 2` and
  `H(t₀) = 2 / (3 t₀)`.

## iii. Table of contents

- A. Time derivatives of curves given by a function of the coordinate
- B. The de Sitter solution
  - B.1. The scale factor and its derivatives
  - B.2. The Friedmann equations
  - B.3. The Hubble and deceleration parameters
- C. The spatially flat power-law solutions
  - C.1. The power-law scale factor and its derivatives
  - C.2. The Hubble and deceleration parameters
  - C.3. The radiation-dominated solution
  - C.4. The Einstein-de Sitter solution
- D. Remaining TODO items

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. Time derivatives of curves given by a function of the coordinate

A curve `t ↦ γ t.val` on `Time` is the pull-back through `toRealCLE` of the curve `γ` on `ℝ`;
its time derivative is the Mathlib derivative of `γ`.

-/

/-- The time derivative of `t ↦ γ t.val` at `t` is the derivative of `γ` at `t.val`. -/
lemma deriv_comp_val {γ : ℝ → ℝ} {t : Time} {v : ℝ} (h : HasDerivAt γ v t.val) :
    ∂ₜ (fun s : Time => γ s.val) t = v :=
  deriv_comp_toRealCLE_of_hasDerivAt γ t v h

/-- The time derivative of any `f : Time → ℝ` at `t` is the derivative at `t.val` of the curve
  `τ ↦ f ⟨τ⟩` on `ℝ`. -/
lemma deriv_eq_of_hasDerivAt {f : Time → ℝ} {t : Time} {v : ℝ}
    (h : HasDerivAt (fun τ : ℝ => f ⟨τ⟩) v t.val) : ∂ₜ f t = v :=
  deriv_comp_toRealCLE_of_hasDerivAt (fun τ : ℝ => f ⟨τ⟩) t v h

/-!

## B. The de Sitter solution

-/

/-!

### B.1. The scale factor and its derivatives

-/

/-- The de Sitter scale factor `a(t) = a₀ exp(σ √(Λ/3) c t)`, for `σ = ±1`
  (the expanding branch is `σ = 1`). -/
noncomputable def deSitterScaleFactor (a₀ σ Λ c : ℝ) : Time → ℝ :=
  fun t => a₀ * Real.exp (σ * √(Λ / 3) * c * t.val)

/-- Mathlib derivative of `y ↦ a₀ exp (K y)`. -/
lemma hasDerivAt_mul_exp_mul (a₀ K x : ℝ) :
    HasDerivAt (fun y : ℝ => a₀ * Real.exp (K * y)) (a₀ * K * Real.exp (K * x)) x := by
  have h := (((hasDerivAt_id x).const_mul K).exp).const_mul a₀
  refine h.congr_deriv ?_
  simp only [id_eq]
  ring

lemma deriv_deSitterScaleFactor (a₀ σ Λ c : ℝ) :
    ∂ₜ (deSitterScaleFactor a₀ σ Λ c) =
      fun t => a₀ * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * t.val) := by
  funext t
  exact deriv_comp_val (hasDerivAt_mul_exp_mul a₀ (σ * √(Λ / 3) * c) t.val)

lemma deriv_deriv_deSitterScaleFactor (a₀ σ Λ c : ℝ) :
    ∂ₜ (∂ₜ (deSitterScaleFactor a₀ σ Λ c)) =
      fun t => a₀ * (σ * √(Λ / 3) * c) * (σ * √(Λ / 3) * c) *
        Real.exp (σ * √(Λ / 3) * c * t.val) := by
  rw [deriv_deSitterScaleFactor]
  funext t
  exact deriv_comp_val
    (hasDerivAt_mul_exp_mul (a₀ * (σ * √(Λ / 3) * c)) (σ * √(Λ / 3) * c) t.val)

/-- `σ² (√(Λ/3))² c² = Λ c² / 3` for `σ = ±1` and `0 ≤ Λ`. -/
lemma sq_deSitterRate {σ Λ c : ℝ} (hΛ : 0 ≤ Λ) (hσ : σ = 1 ∨ σ = -1) :
    (σ * √(Λ / 3) * c) ^ 2 = Λ * c ^ 2 / 3 := by
  have hs : √(Λ / 3) ^ 2 = Λ / 3 := Real.sq_sqrt (by linarith)
  rcases hσ with rfl | rfl <;> linear_combination c ^ 2 * hs

/-!

### B.2. The Friedmann equations

-/

/-- The de Sitter scale factor solves the first-order Friedmann equation with `ρ = 0`,
  `k = 0` and `Λ > 0`. -/
lemma deSitterScaleFactor_firstOrderFriedmann {a₀ σ Λ G c : ℝ} (hΛ : 0 < Λ)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    FirstOrderFriedmann (deSitterScaleFactor a₀ σ Λ c) (fun _ => 0) 0 Λ G c t := by
  unfold FirstOrderFriedmann
  rw [deriv_deSitterScaleFactor]
  simp only [deSitterScaleFactor]
  have he := Real.exp_ne_zero (σ * √(Λ / 3) * c * t.val)
  rw [show a₀ * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * t.val) /
      (a₀ * Real.exp (σ * √(Λ / 3) * c * t.val)) = σ * √(Λ / 3) * c by field_simp,
    sq_deSitterRate hΛ.le hσ]
  ring

/-- The de Sitter scale factor solves the second-order Friedmann equation with `ρ = 0`,
  `p = 0` and `Λ > 0`. -/
lemma deSitterScaleFactor_secondOrderFriedmann {a₀ σ Λ G c : ℝ} (hΛ : 0 < Λ)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    SecondOrderFriedmann (deSitterScaleFactor a₀ σ Λ c) (fun _ => 0) (fun _ => 0) Λ G c t := by
  unfold SecondOrderFriedmann
  rw [deriv_deriv_deSitterScaleFactor]
  simp only [deSitterScaleFactor]
  have he := Real.exp_ne_zero (σ * √(Λ / 3) * c * t.val)
  rw [show a₀ * (σ * √(Λ / 3) * c) * (σ * √(Λ / 3) * c) *
      Real.exp (σ * √(Λ / 3) * c * t.val) / (a₀ * Real.exp (σ * √(Λ / 3) * c * t.val))
      = (σ * √(Λ / 3) * c) ^ 2 by field_simp,
    sq_deSitterRate hΛ.le hσ]
  ring

/-!

### B.3. The Hubble and deceleration parameters

-/

/-- The Hubble parameter of the de Sitter solution is the constant `σ √(Λ/3) c`. -/
lemma hubbleConstant_deSitterScaleFactor {a₀ σ Λ c : ℝ} (ha₀ : a₀ ≠ 0) (t : Time) :
    hubbleConstant (deSitterScaleFactor a₀ σ Λ c) t = σ * √(Λ / 3) * c := by
  unfold hubbleConstant
  rw [deriv_deSitterScaleFactor]
  simp only [deSitterScaleFactor]
  have he := Real.exp_ne_zero (σ * √(Λ / 3) * c * t.val)
  field_simp

/-- The deceleration parameter of the de Sitter solution is `q = -1`. -/
lemma decelerationParameter_deSitterScaleFactor {a₀ σ Λ c : ℝ} (hΛ : 0 < Λ) (hc : 0 < c)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    decelerationParameter (deSitterScaleFactor a₀ σ Λ c) t = -1 := by
  unfold decelerationParameter
  rw [deriv_deriv_deSitterScaleFactor, deriv_deSitterScaleFactor]
  simp only [deSitterScaleFactor]
  have he := Real.exp_ne_zero (σ * √(Λ / 3) * c * t.val)
  have hK : σ * √(Λ / 3) * c ≠ 0 := by
    have hs : 0 < √(Λ / 3) := Real.sqrt_pos.mpr (by linarith)
    rcases hσ with rfl | rfl
    · positivity
    · have : 0 < √(Λ / 3) * c := mul_pos hs hc
      linarith
  have hσ0 : σ ≠ 0 := by
    rcases hσ with rfl | rfl <;> norm_num
  field_simp

/-!

## C. The spatially flat power-law solutions

The radiation-dominated and Einstein-de Sitter solutions are both of the form
`a(t) = (t / t₀) ^ n` for `t > 0`; the Hubble parameter is `n / t` and the deceleration
parameter `(1 - n) / n`. Their densities are imposed by the first-order Friedmann equation with
`k = 0` and `Λ = 0`: `ρ = 3 H² / (8 π G) = 3 n² / (8 π G t²)`.

-/

/-!

### C.1. The power-law scale factor and its derivatives

-/

/-- The power-law scale factor `a(t) = (t / t₀) ^ n` (real power). -/
noncomputable def powerLawScaleFactor (t₀ n : ℝ) : Time → ℝ :=
  fun t => (t.val / t₀) ^ n

/-- Mathlib derivative of `y ↦ (y / t₀) ^ n` away from `y = 0`. -/
lemma hasDerivAt_div_rpow {t₀ : ℝ} (ht₀ : t₀ ≠ 0) (n : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (y / t₀) ^ n) (n / t₀ * (x / t₀) ^ (n - 1)) x := by
  have h := ((hasDerivAt_id x).div_const t₀).rpow_const (p := n)
    (Or.inl (div_ne_zero hx ht₀))
  refine h.congr_deriv ?_
  simp only [id_eq]
  ring

/-- `∂ₜ a = n / t₀ (t / t₀) ^ (n - 1)` away from `t = 0`. -/
lemma deriv_powerLawScaleFactor {t₀ : ℝ} (ht₀ : t₀ ≠ 0) (n : ℝ) {t : Time}
    (ht : t.val ≠ 0) :
    ∂ₜ (powerLawScaleFactor t₀ n) t = n / t₀ * (t.val / t₀) ^ (n - 1) :=
  deriv_comp_val (hasDerivAt_div_rpow ht₀ n ht)

/-- `∂ₜ ∂ₜ a = n (n - 1) / t₀² (t / t₀) ^ (n - 2)` for `t > 0`. The derivative `∂ₜ a` is
  only known away from `t = 0`, which is enough since `t > 0` is an open condition. -/
lemma deriv_deriv_powerLawScaleFactor {t₀ : ℝ} (ht₀ : t₀ ≠ 0) (n : ℝ) {t : Time}
    (ht : 0 < t.val) :
    ∂ₜ (∂ₜ (powerLawScaleFactor t₀ n)) t =
      n / t₀ * ((n - 1) / t₀ * (t.val / t₀) ^ (n - 1 - 1)) := by
  apply deriv_eq_of_hasDerivAt
  have h := (hasDerivAt_div_rpow ht₀ (n - 1) ht.ne').const_mul (n / t₀)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds ht.ne'] with τ hτ
  exact deriv_powerLawScaleFactor ht₀ n (t := ⟨τ⟩) hτ

/-!

### C.2. The Hubble and deceleration parameters

-/

/-- The Hubble parameter of the power-law solution is `n / t` for `t > 0`. -/
lemma hubbleConstant_powerLawScaleFactor {t₀ : ℝ} (ht₀ : 0 < t₀) (n : ℝ) {t : Time}
    (ht : 0 < t.val) :
    hubbleConstant (powerLawScaleFactor t₀ n) t = n / t.val := by
  unfold hubbleConstant
  rw [deriv_powerLawScaleFactor ht₀.ne' n ht.ne', powerLawScaleFactor,
    Real.rpow_sub_one (div_pos ht ht₀).ne']
  have hx : (t.val / t₀) ^ n ≠ 0 := (Real.rpow_pos_of_pos (div_pos ht ht₀) n).ne'
  field_simp

/-- The deceleration parameter of the power-law solution is `(1 - n) / n` for `t > 0`,
  `n ≠ 0`. -/
lemma decelerationParameter_powerLawScaleFactor {t₀ n : ℝ} (ht₀ : 0 < t₀) (hn : n ≠ 0)
    {t : Time} (ht : 0 < t.val) :
    decelerationParameter (powerLawScaleFactor t₀ n) t = (1 - n) / n := by
  unfold decelerationParameter
  rw [deriv_deriv_powerLawScaleFactor ht₀.ne' n ht, deriv_powerLawScaleFactor ht₀.ne' n ht.ne',
    powerLawScaleFactor, Real.rpow_sub_one (div_pos ht ht₀).ne',
    Real.rpow_sub_one (div_pos ht ht₀).ne']
  have hx : (t.val / t₀) ^ n ≠ 0 := (Real.rpow_pos_of_pos (div_pos ht ht₀) n).ne'
  field_simp
  ring

/-- The density imposed on the flat power-law solution by the first-order Friedmann equation,
  `ρ = 3 n² / (8 π G t²)`. -/
noncomputable def powerLawDensity (G n : ℝ) : Time → ℝ :=
  fun t => 3 * n ^ 2 / (8 * π * G * t.val ^ 2)

/-- The flat power-law solution solves the first-order Friedmann equation with `k = 0`,
  `Λ = 0` and the density `powerLawDensity`, for `t > 0`. -/
lemma powerLawScaleFactor_firstOrderFriedmann {t₀ G c : ℝ} (ht₀ : 0 < t₀) (hG : 0 < G)
    (n : ℝ) {t : Time} (ht : 0 < t.val) :
    FirstOrderFriedmann (powerLawScaleFactor t₀ n) (powerLawDensity G n) 0 0 G c t := by
  unfold FirstOrderFriedmann
  have hH := hubbleConstant_powerLawScaleFactor ht₀ n ht
  unfold hubbleConstant at hH
  rw [hH, powerLawDensity]
  have hπ := Real.pi_pos
  field_simp
  ring

/-- The second-order Friedmann equation for the flat power-law solution with the pressure
  `p = w ρ c²`, where `1 + 3 w = 2 (1 - n) / n`, for `t > 0`. -/
lemma powerLawScaleFactor_secondOrderFriedmann {t₀ G c n w : ℝ} (ht₀ : 0 < t₀) (hG : 0 < G)
    (hc : 0 < c) (hn : n ≠ 0) (hw : 1 + 3 * w = 2 * (1 - n) / n) {t : Time} (ht : 0 < t.val) :
    SecondOrderFriedmann (powerLawScaleFactor t₀ n) (powerLawDensity G n)
      (fun s => w * powerLawDensity G n s * c ^ 2) 0 G c t := by
  unfold SecondOrderFriedmann
  simp only [powerLawDensity]
  rw [deriv_deriv_powerLawScaleFactor ht₀.ne' n ht, powerLawScaleFactor,
    Real.rpow_sub_one (div_pos ht ht₀).ne', Real.rpow_sub_one (div_pos ht ht₀).ne']
  have hx : (t.val / t₀) ^ n ≠ 0 := (Real.rpow_pos_of_pos (div_pos ht ht₀) n).ne'
  have hπ := Real.pi_pos
  rw [show w = (2 * (1 - n) / n - 1) / 3 by linarith]
  field_simp
  ring

/-!

### C.3. The radiation-dominated solution

-/

/-- The radiation-dominated scale factor `a(t) = (t / t₀) ^ (1/2)`. -/
noncomputable def radiationScaleFactor (t₀ : ℝ) : Time → ℝ :=
  powerLawScaleFactor t₀ (1 / 2)

/-- The density of the flat radiation-dominated solution, `ρ = 3 / (32 π G t²)`, imposed by
  the first-order Friedmann equation. -/
noncomputable def radiationDensity (G : ℝ) : Time → ℝ :=
  fun t => 3 / (32 * π * G * t.val ^ 2)

/-- The radiation pressure `p = ρ c² / 3`. -/
noncomputable def radiationPressure (G c : ℝ) : Time → ℝ :=
  fun t => radiationDensity G t * c ^ 2 / 3

lemma radiationDensity_eq (G : ℝ) : radiationDensity G = powerLawDensity G (1 / 2) := by
  funext t
  simp only [radiationDensity, powerLawDensity]
  ring

/-- The radiation-dominated solution solves the first-order Friedmann equation with `k = 0`,
  `Λ = 0`, for `t > 0`. -/
lemma radiationScaleFactor_firstOrderFriedmann {t₀ G c : ℝ} (ht₀ : 0 < t₀) (hG : 0 < G)
    {t : Time} (ht : 0 < t.val) :
    FirstOrderFriedmann (radiationScaleFactor t₀) (radiationDensity G) 0 0 G c t := by
  rw [radiationScaleFactor, radiationDensity_eq]
  exact powerLawScaleFactor_firstOrderFriedmann ht₀ hG _ ht

/-- The radiation-dominated solution solves the second-order Friedmann equation with
  `p = ρ c² / 3`, `Λ = 0`, for `t > 0`. -/
lemma radiationScaleFactor_secondOrderFriedmann {t₀ G c : ℝ} (ht₀ : 0 < t₀) (hG : 0 < G)
    (hc : 0 < c) {t : Time} (ht : 0 < t.val) :
    SecondOrderFriedmann (radiationScaleFactor t₀) (radiationDensity G) (radiationPressure G c)
      0 G c t := by
  have h := powerLawScaleFactor_secondOrderFriedmann (w := 1 / 3) ht₀ hG hc
    (by norm_num : (1 / 2 : ℝ) ≠ 0) (by norm_num) ht
  rw [radiationScaleFactor, radiationDensity_eq]
  convert h using 2
  simp only [radiationPressure, radiationDensity_eq]
  ring

/-- The deceleration parameter of the radiation-dominated solution is `q = 1`. -/
lemma decelerationParameter_radiationScaleFactor {t₀ : ℝ} (ht₀ : 0 < t₀) {t : Time}
    (ht : 0 < t.val) :
    decelerationParameter (radiationScaleFactor t₀) t = 1 := by
  rw [radiationScaleFactor, decelerationParameter_powerLawScaleFactor ht₀ (by norm_num) ht]
  norm_num

/-- `H(t₀) = 1 / (2 t₀)` for the radiation-dominated solution, that is `t₀ = 1 / (2 H₀)`. -/
lemma hubbleConstant_radiationScaleFactor_t₀ {t₀ : ℝ} (ht₀ : 0 < t₀) :
    hubbleConstant (radiationScaleFactor t₀) ⟨t₀⟩ = 1 / (2 * t₀) := by
  rw [radiationScaleFactor, hubbleConstant_powerLawScaleFactor ht₀ _ ht₀]
  ring

/-!

### C.4. The Einstein-de Sitter solution

-/

/-- The Einstein-de Sitter (flat, dust) scale factor `a(t) = (t / t₀) ^ (2/3)`. -/
noncomputable def einsteinDeSitterScaleFactor (t₀ : ℝ) : Time → ℝ :=
  powerLawScaleFactor t₀ (2 / 3)

/-- The dust density of the Einstein-de Sitter solution, `ρ = 1 / (6 π G t²)`, imposed by the
  first-order Friedmann equation. -/
noncomputable def einsteinDeSitterDensity (G : ℝ) : Time → ℝ :=
  fun t => 1 / (6 * π * G * t.val ^ 2)

lemma einsteinDeSitterDensity_eq (G : ℝ) :
    einsteinDeSitterDensity G = powerLawDensity G (2 / 3) := by
  funext t
  simp only [einsteinDeSitterDensity, powerLawDensity]
  ring

/-- The Einstein-de Sitter solution solves the first-order Friedmann equation with `k = 0`,
  `Λ = 0`, for `t > 0`. -/
lemma einsteinDeSitterScaleFactor_firstOrderFriedmann {t₀ G c : ℝ} (ht₀ : 0 < t₀)
    (hG : 0 < G) {t : Time} (ht : 0 < t.val) :
    FirstOrderFriedmann (einsteinDeSitterScaleFactor t₀) (einsteinDeSitterDensity G)
      0 0 G c t := by
  rw [einsteinDeSitterScaleFactor, einsteinDeSitterDensity_eq]
  exact powerLawScaleFactor_firstOrderFriedmann ht₀ hG _ ht

/-- The Einstein-de Sitter solution solves the second-order Friedmann equation with `p = 0`,
  `Λ = 0`, for `t > 0`. -/
lemma einsteinDeSitterScaleFactor_secondOrderFriedmann {t₀ G c : ℝ} (ht₀ : 0 < t₀)
    (hG : 0 < G) (hc : 0 < c) {t : Time} (ht : 0 < t.val) :
    SecondOrderFriedmann (einsteinDeSitterScaleFactor t₀) (einsteinDeSitterDensity G)
      (fun _ => 0) 0 G c t := by
  have h := powerLawScaleFactor_secondOrderFriedmann (w := 0) ht₀ hG hc
    (by norm_num : (2 / 3 : ℝ) ≠ 0) (by norm_num) ht
  rw [einsteinDeSitterScaleFactor, einsteinDeSitterDensity_eq]
  convert h using 2
  ring

/-- The deceleration parameter of the Einstein-de Sitter solution is `q = 1 / 2`. -/
lemma decelerationParameter_einsteinDeSitterScaleFactor {t₀ : ℝ} (ht₀ : 0 < t₀) {t : Time}
    (ht : 0 < t.val) :
    decelerationParameter (einsteinDeSitterScaleFactor t₀) t = 1 / 2 := by
  rw [einsteinDeSitterScaleFactor,
    decelerationParameter_powerLawScaleFactor ht₀ (by norm_num) ht]
  norm_num

/-- `H(t₀) = 2 / (3 t₀)` for the Einstein-de Sitter solution, that is `t₀ = 2 / (3 H₀)`. -/
lemma hubbleConstant_einsteinDeSitterScaleFactor_t₀ {t₀ : ℝ} (ht₀ : 0 < t₀) :
    hubbleConstant (einsteinDeSitterScaleFactor t₀) ⟨t₀⟩ = 2 / (3 * t₀) := by
  rw [einsteinDeSitterScaleFactor, hubbleConstant_powerLawScaleFactor ht₀ _ ht₀]
  ring

/-!

## D. Remaining TODO items

-/

TODO "Prove that the Milne solution `a = c t` (empty universe, `K < 0`) has
  vanishing scalar curvature, i.e. it is Minkowski space in expanding coordinates."

TODO "Define the Einstein static universe (`∂ₜ a = ∂ₜ ∂ₜ a = 0`, forcing `K > 0`
  and `ρ_m = 2 ρ_Λ`) and prove that it is an unstable equilibrium."

end Cosmology.FLRW.FriedmannEquation
