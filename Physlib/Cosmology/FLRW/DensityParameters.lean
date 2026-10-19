/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Cosmology.FLRW.MatterContent
/-!

# Density parameters and the closure relation

## i. Overview

The first-order Friedmann equation of `Physlib.Cosmology.FLRW.Basic`,
`H² = (8 π G / 3) ρ - k c² / a² + Λ c² / 3`, can be read as a budget for the expansion rate `H`.

The reference quantity is the critical density `ρ_cr = 3 H² / (8 π G)`. It is the mass density
for which this equation holds with `k = 0` and `Λ = 0`: the density of a spatially flat universe
without cosmological constant expanding at the rate `H`. It is called critical because, when
`Λ = 0`, a universe denser than `ρ_cr` is spatially closed (`k > 0`), a less dense one is open
(`k < 0`), and a universe at exactly `ρ_cr` is flat. It depends on time through `H`.

Each term of the equation is then measured in units of `ρ_cr`, which gives dimensionless
quantities:
- the density parameter `Ω = ρ / ρ_cr` of a component of mass density `ρ`;
- the cosmological-constant density parameter `Ω_Λ = Λ c² / (3 H²)`, which is the density
  parameter of the uniform density `ρ_Λ = Λ c² / (8 π G)` equivalent to `Λ`;
- the curvature density parameter `Ω_K = - k c² / (H² a²)`, which is not the density of a fluid
  but the share of the budget carried by spatial curvature.

Dividing the Friedmann equation by `H²` gives the closure relation `Ω + Ω_Λ + Ω_K = 1`.

These quantities are defined for an FLRW model `U`: `U.criticalDensity G t`,
`U.densityParameter F G t` for a cosmic fluid `F`, `U.curvatureDensityParameter c t`, with `k`
the curvature parameter of the spatial geometry of `U`, and `U.lambdaDensityParameter Λ c t`. If
`U`, filled with `F`, solves the Friedmann equations, the closure relation holds at every time of
its interval at which `H ≠ 0`.

The reduced Hubble function of the standard cosmological model, built from these parameters, is
in `Physlib.Cosmology.FLRW.ReducedHubble`, and the age of the universe in
`Physlib.Cosmology.FLRW.Age`.

## ii. Key results

- `FLRW.criticalDensity`, `FLRW.densityParameter`, `FLRW.curvatureDensityParameter`,
  `FLRW.lambdaDensityParameter`: the critical density and the density parameters of an FLRW
  model.
- `FLRW.lambdaDensityParameter_eq_densityParameter`: `Ω_Λ` is the density parameter of the
  cosmological constant as a fluid; `FLRW.densityParameter_addCosmologicalConstant`: folding the
  cosmological constant into the fluid adds `Ω_Λ` to its density parameter.
- `FLRW.FriedmannSolution.densityParameter_add_lambda_add_curvature`: the closure relation
  `Ω + Ω_Λ + Ω_K = 1` for a solution of the Friedmann equations;
  `FLRW.FriedmannSolution.densityParameter_add_curvature`: `Ω + Ω_K = 1` when `Λ = 0`.

## iii. Table of contents

- A. The critical density and the density parameters
- B. The closure relation

-/

@[expose] public section

namespace Cosmology.FLRW

open Real Time FriedmannEquation

variable (U : FLRW)

/-!

## A. The critical density and the density parameters

With the convention `x / 0 = 0`, these quantities vanish when `H = 0` or `G = 0`; they carry their
physical meaning at the times of the interval of the model at which `H ≠ 0`.

-/

/-- The critical density `ρ_cr = 3 H² / (8 π G)` of the FLRW model `U` at the time `t`, `H` being
  the Hubble parameter of its scale factor: the mass density for which the first-order Friedmann
  equation holds with `k = 0` and `Λ = 0` at the expansion rate `H`, that is, the density of a
  spatially flat universe without cosmological constant. It is the unit in which the density
  parameters are measured, and it depends on time through `H`. -/
noncomputable def criticalDensity (G : ℝ) (t : Time) : ℝ :=
  3 * hubbleConstant U.a t ^ 2 / (8 * π * G)

/-- The density parameter `Ω = ρ / ρ_cr` of the cosmic fluid `F` in the FLRW model `U`: its density
  `F.ρ` in units of the critical density. It is dimensionless; for a solution of the Friedmann
  equations without cosmological constant, `Ω = 1` at a time at which `H ≠ 0` exactly when
  `Ω_K = 0` (see `FLRW.FriedmannSolution.densityParameter_add_curvature`). -/
noncomputable def densityParameter (F : CosmicFluid) (G : ℝ) (t : Time) : ℝ :=
  F.ρ t / U.criticalDensity G t

/-- The curvature density parameter `Ω_K = - k c² / (H² a²)` of the FLRW model `U`, with
  `a = U.a t`, `H` the Hubble parameter of `U.a` and `k` the curvature parameter of the spatial
  geometry of `U`: the share of the first-order Friedmann equation carried by the spatial
  curvature, in the same units as the density parameters. It is not the density of a fluid; when
  `H`, `a` and `c` are nonzero, it is positive for a saddle geometry and negative for a spherical
  one (see `SpatialGeometry.curvature_saddle_neg` and `SpatialGeometry.curvature_spherical_pos`),
  and it is zero for the flat one. -/
noncomputable def curvatureDensityParameter (c : ℝ) (t : Time) : ℝ :=
  -U.geometry.curvature * c ^ 2 / (hubbleConstant U.a t ^ 2 * U.a t ^ 2)

/-- The cosmological-constant density parameter `Ω_Λ = Λ c² / (3 H²)` of the FLRW model `U`: the
  share of the first-order Friedmann equation carried by the cosmological constant. For `G ≠ 0`, it
  is the density parameter of the cosmological constant as a fluid of density
  `ρ_Λ = Λ c² / (8 π G)` (see `lambdaDensityParameter_eq_densityParameter`). -/
noncomputable def lambdaDensityParameter (Λ c : ℝ) (t : Time) : ℝ :=
  Λ * c ^ 2 / (3 * hubbleConstant U.a t ^ 2)

/-- `Ω_Λ` is the density parameter of the cosmological constant as a fluid, the empty fluid with
  the cosmological constant folded in, for `G ≠ 0`. -/
lemma lambdaDensityParameter_eq_densityParameter {Λ G c : ℝ} (hG : G ≠ 0) (t : Time) :
    U.lambdaDensityParameter Λ c t
      = U.densityParameter (CosmicFluid.empty.addCosmologicalConstant Λ G c) G t := by
  simp only [lambdaDensityParameter, densityParameter, criticalDensity, CosmicFluid.empty,
    CosmicFluid.addCosmologicalConstant, cosmologicalConstantDensity, zero_add]
  have hπ := Real.pi_ne_zero
  field_simp

/-- Folding the cosmological constant into the cosmic fluid adds `Ω_Λ` to its density parameter:
  the density parameter of `F.addCosmologicalConstant Λ G c` is `Ω + Ω_Λ`, for `G ≠ 0`. -/
lemma densityParameter_addCosmologicalConstant (F : CosmicFluid) {Λ G c : ℝ} (hG : G ≠ 0)
    (t : Time) :
    U.densityParameter (F.addCosmologicalConstant Λ G c) G t
      = U.densityParameter F G t + U.lambdaDensityParameter Λ c t := by
  rw [U.lambdaDensityParameter_eq_densityParameter hG]
  simp only [densityParameter, CosmicFluid.empty, CosmicFluid.addCosmologicalConstant, zero_add,
    add_div]

/-!

## B. The closure relation

-/

namespace FriedmannSolution

variable {U} {F : CosmicFluid} {Λ G c : ℝ}

/-- If the FLRW model `U` filled with the cosmic fluid `F` solves the Friedmann equations, the
  closure relation `Ω + Ω_Λ + Ω_K = 1`, a rearrangement of the first-order Friedmann equation,
  holds at every time of the interval `U.I` at which `H ≠ 0`. -/
lemma densityParameter_add_lambda_add_curvature (h : U.FriedmannSolution F Λ G c) {t : Time}
    (ht : t ∈ U.I) (hH : hubbleConstant U.a t ≠ 0) :
    U.densityParameter F G t + U.lambdaDensityParameter Λ c t
      + U.curvatureDensityParameter c t = 1 := by
  have hF1 := h.firstOrder t ht
  unfold densityParameter lambdaDensityParameter curvatureDensityParameter criticalDensity
  unfold FirstOrderFriedmann at hF1
  unfold hubbleConstant at hH ⊢
  have hπ := Real.pi_ne_zero
  have ha := U.a_ne_zero ht
  have key : F.ρ t / (3 * (∂ₜ U.a t / U.a t) ^ 2 / (8 * π * G))
      + Λ * c ^ 2 / (3 * (∂ₜ U.a t / U.a t) ^ 2)
      + -U.geometry.curvature * c ^ 2 / ((∂ₜ U.a t / U.a t) ^ 2 * U.a t ^ 2)
      = (8 * π * G / 3 * F.ρ t - U.geometry.curvature * c ^ 2 / U.a t ^ 2 + Λ * c ^ 2 / 3)
        / (∂ₜ U.a t / U.a t) ^ 2 := by
    field_simp
    ring
  rw [key, ← hF1, div_self (pow_ne_zero 2 hH)]

/-- If the FLRW model `U` filled with the cosmic fluid `F` solves the Friedmann equations without
  cosmological constant, the closure relation `Ω + Ω_K = 1` holds at every time of the interval
  `U.I` at which `H ≠ 0`. -/
lemma densityParameter_add_curvature (h : U.FriedmannSolution F 0 G c) {t : Time} (ht : t ∈ U.I)
    (hH : hubbleConstant U.a t ≠ 0) :
    U.densityParameter F G t + U.curvatureDensityParameter c t = 1 := by
  have h1 := h.densityParameter_add_lambda_add_curvature ht hH
  simpa [lambdaDensityParameter] using h1

end FriedmannSolution

end Cosmology.FLRW
