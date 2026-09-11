/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.MatterContent
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-!

# Exact solutions of the Friedmann equations

## i. Overview

This file collects the standard closed-form solutions of the Friedmann equations
(`FirstOrderFriedmann` and `SecondOrderFriedmann` of `Physlib.Cosmology.FLRW.Basic`) and
proves that they solve them: the de Sitter solution, the spatially flat power-law
solutions (radiation-dominated and Einstein-de Sitter), the Milne model, and the equilibrium
relations of the Einstein static universe. The vanishing of the curvature of the Milne model
and the instability of the Einstein static universe are still TODO items: neither the curvature
of the FLRW metric nor a perturbation theory of the Friedmann equations is available yet.

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
- `milneScaleFactor_firstOrderFriedmann`, `milneScaleFactor_secondOrderFriedmann`: the Milne
  scale factor `a = c t` solves the empty (`ρ = 0`, `p = 0`, `Λ = 0`) Friedmann equations with
  `k = -1`; `q = 0`.
- `einsteinStatic_density`, `einsteinStatic_curvature`: if `∂ₜ a = ∂ₜ ∂ₜ a = 0` at `t` and the
  Friedmann equations hold there with `p = 0`, then `ρ = Λ c² / (4 π G) = 2 ρ_Λ` and
  `k c² / a² = 4 π G ρ`, so that `k > 0` when `ρ > 0` (`einsteinStatic_curvature_pos`).

## iii. Table of contents

- A. The de Sitter solution
  - A.1. The scale factor and its derivatives
  - A.2. The Friedmann equations
  - A.3. The Hubble and deceleration parameters
- B. The spatially flat power-law solutions
  - B.1. The power-law scale factor and its derivatives
  - B.2. The Hubble and deceleration parameters
  - B.3. The radiation-dominated solution
  - B.4. The Einstein-de Sitter solution
- C. The Milne solution
- D. The Einstein static universe
- E. Remaining TODO items

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The de Sitter solution

-/

/-!

### A.1. The scale factor and its derivatives

-/

/-- The de Sitter scale factor `a(t) = a₀ exp(σ √(Λ/3) c t)`, for `σ = ±1`
  (the expanding branch is `σ = 1`). -/
noncomputable def deSitterScaleFactor (a₀ σ Λ c : ℝ) : Time → ℝ :=
  fun t => a₀ * Real.exp (σ * √(Λ / 3) * c * t.val)

lemma deriv_deSitterScaleFactor (a₀ σ Λ c : ℝ) :
    ∂ₜ (deSitterScaleFactor a₀ σ Λ c) =
      fun t => a₀ * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * t.val) := by
  funext t
  have h : HasDerivAt (fun y : ℝ => a₀ * Real.exp (σ * √(Λ / 3) * c * y))
      (a₀ * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * t.val)) t.val := by
    have h := (((hasDerivAt_id t.val).const_mul (σ * √(Λ / 3) * c)).exp).const_mul a₀
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  exact deriv_comp_val h

lemma deriv_deriv_deSitterScaleFactor (a₀ σ Λ c : ℝ) :
    ∂ₜ (∂ₜ (deSitterScaleFactor a₀ σ Λ c)) =
      fun t => a₀ * (σ * √(Λ / 3) * c) * (σ * √(Λ / 3) * c) *
        Real.exp (σ * √(Λ / 3) * c * t.val) := by
  rw [deriv_deSitterScaleFactor]
  funext t
  have h : HasDerivAt (fun y : ℝ => a₀ * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * y))
      (a₀ * (σ * √(Λ / 3) * c) * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * t.val))
      t.val := by
    have h := (((hasDerivAt_id t.val).const_mul (σ * √(Λ / 3) * c)).exp).const_mul
      (a₀ * (σ * √(Λ / 3) * c))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  exact deriv_comp_val h

/-- `σ² (√(Λ/3))² c² = Λ c² / 3` for `σ = ±1` and `0 ≤ Λ`. -/
lemma sq_deSitterRate {σ Λ c : ℝ} (hΛ : 0 ≤ Λ) (hσ : σ = 1 ∨ σ = -1) :
    (σ * √(Λ / 3) * c) ^ 2 = Λ * c ^ 2 / 3 := by
  have hs : √(Λ / 3) ^ 2 = Λ / 3 := Real.sq_sqrt (by linarith)
  rcases hσ with rfl | rfl <;> linear_combination c ^ 2 * hs

/-!

### A.2. The Friedmann equations

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

### A.3. The Hubble and deceleration parameters

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

## B. The spatially flat power-law solutions

The radiation-dominated and Einstein-de Sitter solutions are both of the form
`a(t) = (t / t₀) ^ n` for `t > 0`; the Hubble parameter is `n / t` and the deceleration
parameter `(1 - n) / n`. Their densities are imposed by the first-order Friedmann equation with
`k = 0` and `Λ = 0`: `ρ = 3 H² / (8 π G) = 3 n² / (8 π G t²)`.

-/

/-!

### B.1. The power-law scale factor and its derivatives

-/

/-- The power-law scale factor `a(t) = (t / t₀) ^ n` (real power). -/
noncomputable def powerLawScaleFactor (t₀ n : ℝ) : Time → ℝ :=
  fun t => (t.val / t₀) ^ n

/-- `∂ₜ a = n / t₀ (t / t₀) ^ (n - 1)` away from `t = 0`. -/
lemma deriv_powerLawScaleFactor {t₀ : ℝ} (ht₀ : t₀ ≠ 0) (n : ℝ) {t : Time}
    (ht : t.val ≠ 0) :
    ∂ₜ (powerLawScaleFactor t₀ n) t = n / t₀ * (t.val / t₀) ^ (n - 1) := by
  have h : HasDerivAt (fun y : ℝ => (y / t₀) ^ n) (n / t₀ * (t.val / t₀) ^ (n - 1)) t.val := by
    have h := ((hasDerivAt_id t.val).div_const t₀).rpow_const (p := n)
      (Or.inl (div_ne_zero ht ht₀))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  exact deriv_comp_val h

/-- `∂ₜ ∂ₜ a = n (n - 1) / t₀² (t / t₀) ^ (n - 2)` for `t > 0`. The derivative `∂ₜ a` is
  only known away from `t = 0`, which is enough since `t > 0` is an open condition. -/
lemma deriv_deriv_powerLawScaleFactor {t₀ : ℝ} (ht₀ : t₀ ≠ 0) (n : ℝ) {t : Time}
    (ht : 0 < t.val) :
    ∂ₜ (∂ₜ (powerLawScaleFactor t₀ n)) t =
      n / t₀ * ((n - 1) / t₀ * (t.val / t₀) ^ (n - 1 - 1)) := by
  apply deriv_eq_of_hasDerivAt
  have h₁ : HasDerivAt (fun y : ℝ => (y / t₀) ^ (n - 1))
      ((n - 1) / t₀ * (t.val / t₀) ^ (n - 1 - 1)) t.val := by
    have h := ((hasDerivAt_id t.val).div_const t₀).rpow_const (p := n - 1)
      (Or.inl (div_ne_zero ht.ne' ht₀))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have h := h₁.const_mul (n / t₀)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds ht.ne'] with τ hτ
  exact deriv_powerLawScaleFactor ht₀ n (t := ⟨τ⟩) hτ

/-!

### B.2. The Hubble and deceleration parameters

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

### B.3. The radiation-dominated solution

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

### B.4. The Einstein-de Sitter solution

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

## C. The Milne solution

The Milne universe is the empty (`ρ = 0`, `p = 0`, `Λ = 0`) solution with `k = -1` and
`a(t) = c t` for `t > 0`. That it is Minkowski space in expanding coordinates (vanishing
curvature) is not stated here: the FLRW metric is not yet an object of Physlib.

-/

/-- The Milne scale factor `a(t) = c t`. -/
noncomputable def milneScaleFactor (c : ℝ) : Time → ℝ :=
  fun t => c * t.val

lemma deriv_milneScaleFactor (c : ℝ) : ∂ₜ (milneScaleFactor c) = fun _ => c := by
  funext t
  exact deriv_comp_val (((hasDerivAt_id t.val).const_mul c).congr_deriv (mul_one c))

lemma deriv_deriv_milneScaleFactor (c : ℝ) : ∂ₜ (∂ₜ (milneScaleFactor c)) = fun _ => 0 := by
  rw [deriv_milneScaleFactor]
  funext t
  exact deriv_comp_val (γ := fun _ => c) (hasDerivAt_const t.val c)

/-- The Milne solution solves the first-order Friedmann equation with `ρ = 0`, `k = -1` and
  `Λ = 0`, for `t > 0`. -/
lemma milneScaleFactor_firstOrderFriedmann {G c : ℝ} (hc : 0 < c) {t : Time} (ht : 0 < t.val) :
    FirstOrderFriedmann (milneScaleFactor c) (fun _ => 0) (-1) 0 G c t := by
  unfold FirstOrderFriedmann
  rw [deriv_milneScaleFactor]
  simp only [milneScaleFactor]
  field_simp
  ring

/-- The Milne solution solves the second-order Friedmann equation with `ρ = 0`, `p = 0` and
  `Λ = 0`. -/
lemma milneScaleFactor_secondOrderFriedmann {G c : ℝ} (t : Time) :
    SecondOrderFriedmann (milneScaleFactor c) (fun _ => 0) (fun _ => 0) 0 G c t := by
  unfold SecondOrderFriedmann
  rw [deriv_deriv_milneScaleFactor]
  simp

/-- The deceleration parameter of the Milne solution is `q = 0`. -/
lemma decelerationParameter_milneScaleFactor (c : ℝ) (t : Time) :
    decelerationParameter (milneScaleFactor c) t = 0 := by
  unfold decelerationParameter
  rw [deriv_deriv_milneScaleFactor, deriv_milneScaleFactor]
  simp

/-!

## D. The Einstein static universe

At an instant where `∂ₜ a = ∂ₜ ∂ₜ a = 0`, the two Friedmann equations with dust (`p = 0`)
force the density `ρ = Λ c² / (4 π G)`, twice the density `cosmologicalConstantDensity`
(`ρ_Λ = Λ c² / (8 π G)`, defined in `Physlib.Cosmology.FLRW.MatterContent`), and
`k c² / a² = 4 π G ρ`, hence a positive curvature parameter when `ρ > 0`. That this
equilibrium is unstable is not stated here.

-/

/-- In the Einstein static universe the dust density is `ρ = Λ c² / (4 π G) = 2 ρ_Λ`. -/
lemma einsteinStatic_density {a ρ : Time → ℝ} {Λ G c : ℝ} {t : Time} (hG : 0 < G)
    (h2 : ∂ₜ (∂ₜ a) t = 0) (hF2 : SecondOrderFriedmann a ρ (fun _ => 0) Λ G c t) :
    ρ t = 2 * cosmologicalConstantDensity Λ G c := by
  unfold SecondOrderFriedmann at hF2
  rw [h2, zero_div] at hF2
  simp only [mul_zero, zero_div, add_zero] at hF2
  unfold cosmologicalConstantDensity
  have hπ := Real.pi_pos
  field_simp
  linarith

/-- In the Einstein static universe `k c² / a² = 4 π G ρ`. -/
lemma einsteinStatic_curvature {a ρ : Time → ℝ} {k Λ G c : ℝ} {t : Time}
    (h1 : ∂ₜ a t = 0) (h2 : ∂ₜ (∂ₜ a) t = 0) (hF1 : FirstOrderFriedmann a ρ k Λ G c t)
    (hF2 : SecondOrderFriedmann a ρ (fun _ => 0) Λ G c t) :
    k * c ^ 2 / (a t) ^ 2 = 4 * π * G * ρ t := by
  unfold FirstOrderFriedmann at hF1
  unfold SecondOrderFriedmann at hF2
  rw [h1, zero_div] at hF1
  rw [h2, zero_div] at hF2
  simp only [mul_zero, zero_div, add_zero] at hF1 hF2
  linarith

/-- In the Einstein static universe with positive density, the curvature parameter is
  positive. -/
lemma einsteinStatic_curvature_pos {a ρ : Time → ℝ} {k Λ G c : ℝ} {t : Time} (hG : 0 < G)
    (hc : 0 < c) (ha : a t ≠ 0) (hρ : 0 < ρ t) (h1 : ∂ₜ a t = 0) (h2 : ∂ₜ (∂ₜ a) t = 0)
    (hF1 : FirstOrderFriedmann a ρ k Λ G c t)
    (hF2 : SecondOrderFriedmann a ρ (fun _ => 0) Λ G c t) :
    0 < k := by
  have h := einsteinStatic_curvature h1 h2 hF1 hF2
  have hpos : 0 < k * c ^ 2 / (a t) ^ 2 := by
    rw [h]
    positivity
  have ha2 : 0 < (a t) ^ 2 := by positivity
  have hc2 : 0 < c ^ 2 := by positivity
  rw [div_pos_iff_of_pos_right ha2] at hpos
  exact (mul_pos_iff_of_pos_right hc2).mp hpos

/-!

## E. Remaining TODO items

-/

TODO "Prove that the Milne solution `milneScaleFactor` (empty universe, `K < 0`) has
  vanishing scalar curvature, i.e. it is Minkowski space in expanding coordinates."

TODO "Prove that the Einstein static universe (`∂ₜ a = ∂ₜ ∂ₜ a = 0`, `einsteinStatic_density`,
  `einsteinStatic_curvature`) is an unstable equilibrium."

end Cosmology.FLRW.FriedmannEquation
