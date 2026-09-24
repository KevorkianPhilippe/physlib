/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import PhyslibAlpha.ClassicalMechanics.GalileanMass
public import Mathlib.Algebra.Lie.Cochain
/-!

# The second cohomology of the Galilean Lie algebra (Souriau)

## i. Overview

Souriau states (12.131), p. 152, that the space of symplectic cohomology of the Galilean group
has dimension `1`: every symplectic cocycle is `θ(a) = a • μ₀ - μ₀ + m θ₀(a)` (12.132), with
derivative `f(Z)(Z') = μ₀[Z, Z'] + m f₀(Z)(Z')` at the identity (12.133), and the number `m`
locates the class. He does not carry out the computation, which he calls long but elementary, and
refers to V. Bargmann (Ann. Math. 59, 1954). This file carries it out at the level of the Lie
algebra, where the derivative `f` of a symplectic cocycle is an antisymmetric bilinear form
satisfying the cyclic identity (11.33) (p. 116; (11.30), (11.32)).

In Mathlib's vocabulary (`LieModule.Cohomology`), such an `f` is a 2-cocycle of the Lie algebra
with coefficients in the trivial module `ℝ` (`mem_twoCocycle_iff_of_trivial` is (11.33) for an
alternating form), and the coboundaries `d₁₂ φ (Z, Z') = -φ([Z, Z'])` are Souriau's `μ₀[Z, Z']`
(p. 116, note (1); (11.24), p. 114) up to the sign of `μ₀`. The file gives the Galilean Lie algebra
of `PhyslibAlpha.ClassicalMechanics.GalileanMass` its real vector space and Lie algebra structures
(the bracket is Souriau's), and proves that every real 2-cocycle is a coboundary plus a multiple
of `f₀`, the multiple being its mass `c(B e₁)(T e₁)` (a change of velocity and a space translation
along the same axis). The mass is a surjective linear map whose kernel is the coboundaries, so
the 2-cocycles modulo the coboundaries are isomorphic to `ℝ`: this is (12.131) at the level of
the algebra.

The computation is organised by blocks (rotations `R`, changes of velocity `B`, space
translations `T`, time translation `H`): no term between two space translations, two changes of
velocity, the time translation and a space translation, a rotation and the time translation; an
isotropic term `⟨β, γ⟩ m` between a change of velocity and a space translation; the remaining
blocks are read off a torsor `μ₀ = {l, g, p, E}`. This organisation is the file's own.

What is not formalised here:
- the level of the group, (12.131)-(12.132) as printed: the passage from a group cocycle to its
  derivative ((11.22 b), (11.32)) and back, which uses the connectedness of the group (p. 139,
  (11.22 c)) and differentiability;
- the quotient itself: Mathlib's `LieModule.Cohomology` does not yet define coboundaries or
  cohomology, and the statement is given as `ker_massOf` and `massOf_surjective`; the dimension `9`
  of the coboundaries is not stated;
- other dimensions of space: the computation is done in `ℝ³`.

## ii. Key results

- `GalileanAlgebra.instLieAlgebra`: the Galilean Lie algebra is a real Lie algebra for
  Souriau's bracket.
- `GalileanAlgebra.massTwoCocycle`: (12.129), `f₀` is a 2-cocycle with real coefficients.
- `GalileanAlgebra.twoCocycle_eq_d₁₂_add_smul`: (12.133) at the level of the algebra, every real
  2-cocycle is a coboundary plus its mass times `f₀`.
- `GalileanAlgebra.mem_twoCoboundary_iff`, `GalileanAlgebra.ker_massOf`,
  `GalileanAlgebra.massOf_surjective`: (12.131) at the level of the algebra, the 2-cocycles modulo
  the coboundaries are isomorphic to `ℝ` by the mass.
- `GalileanAlgebra.massTwoCocycle_not_mem_twoCoboundary`: `f₀` is not a coboundary.

## iii. Table of contents

- A. The Galilean Lie algebra as a real Lie algebra
- B. The real 2-cocycles and the mass cocycle
- C. The computation
- D. Every real 2-cocycle is a coboundary plus a multiple of `f₀`
- E. The mass classifies the 2-cocycles up to coboundaries

## iv. References

- J.-M. Souriau, Structure des systèmes dynamiques, Dunod, Paris, 1970: p. 152 (12.131)-(12.133);
  p. 151 (12.129)-(12.130); p. 113 (11.22), p. 114 (11.24), p. 115 (11.30), p. 116 (11.32)-(11.33)
  and note (1); p. 139 for the connectedness of the group.

## References

* J.-M. Souriau, *Structure des systèmes dynamiques*, Maîtrises de mathématiques, Dunod,
  Paris, 1970: chapter 12, pp. 139-152, and pp. 113-116 for (11.22)-(11.33). The equation numbers
  refer to this edition. [ref: Souriau1970]

-/

@[expose] public section

noncomputable section

namespace ClassicalMechanics

open Matrix LieModule.Cohomology

local notation "ℝ³" => Fin 3 → ℝ

namespace GalileanAlgebra

/-!

## A. The Galilean Lie algebra as a real Lie algebra

-/

/-- The components `(ω, β, γ, ε)` of an element of the Galilean Lie algebra. -/
def toProd (Z : GalileanAlgebra) : ℝ³ × ℝ³ × ℝ³ × ℝ := (Z.ω, Z.β, Z.γ, Z.ε)

lemma toProd_injective : Function.Injective toProd := fun Z Z' h => by
  simp only [toProd, Prod.mk.injEq] at h
  exact GalileanAlgebra.ext h.1 h.2.1 h.2.2.1 h.2.2.2

instance : Neg GalileanAlgebra := ⟨fun Z => ⟨-Z.ω, -Z.β, -Z.γ, -Z.ε⟩⟩

instance : Sub GalileanAlgebra := ⟨fun Z Z' => ⟨Z.ω - Z'.ω, Z.β - Z'.β, Z.γ - Z'.γ, Z.ε - Z'.ε⟩⟩

instance : SMul ℕ GalileanAlgebra := ⟨fun n Z => ⟨n • Z.ω, n • Z.β, n • Z.γ, n • Z.ε⟩⟩

instance : SMul ℤ GalileanAlgebra := ⟨fun n Z => ⟨n • Z.ω, n • Z.β, n • Z.γ, n • Z.ε⟩⟩

instance : SMul ℝ GalileanAlgebra := ⟨fun c Z => ⟨c • Z.ω, c • Z.β, c • Z.γ, c • Z.ε⟩⟩

/-- The Galilean Lie algebra is a real vector space, component by component. -/
instance : AddCommGroup GalileanAlgebra :=
  toProd_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℝ GalileanAlgebra :=
  toProd_injective.module ℝ ⟨⟨toProd, rfl⟩, fun _ _ => rfl⟩ (fun _ _ => rfl)

@[simp] lemma zero_ω : (0 : GalileanAlgebra).ω = 0 := rfl
@[simp] lemma zero_β : (0 : GalileanAlgebra).β = 0 := rfl
@[simp] lemma zero_γ : (0 : GalileanAlgebra).γ = 0 := rfl
@[simp] lemma zero_ε : (0 : GalileanAlgebra).ε = 0 := rfl
@[simp] lemma add_ω (Z Z' : GalileanAlgebra) : (Z + Z').ω = Z.ω + Z'.ω := rfl
@[simp] lemma add_β (Z Z' : GalileanAlgebra) : (Z + Z').β = Z.β + Z'.β := rfl
@[simp] lemma add_γ (Z Z' : GalileanAlgebra) : (Z + Z').γ = Z.γ + Z'.γ := rfl
@[simp] lemma add_ε (Z Z' : GalileanAlgebra) : (Z + Z').ε = Z.ε + Z'.ε := rfl
@[simp] lemma neg_ω (Z : GalileanAlgebra) : (-Z).ω = -Z.ω := rfl
@[simp] lemma neg_β (Z : GalileanAlgebra) : (-Z).β = -Z.β := rfl
@[simp] lemma neg_γ (Z : GalileanAlgebra) : (-Z).γ = -Z.γ := rfl
@[simp] lemma neg_ε (Z : GalileanAlgebra) : (-Z).ε = -Z.ε := rfl
@[simp] lemma sub_ω (Z Z' : GalileanAlgebra) : (Z - Z').ω = Z.ω - Z'.ω := rfl
@[simp] lemma sub_β (Z Z' : GalileanAlgebra) : (Z - Z').β = Z.β - Z'.β := rfl
@[simp] lemma sub_γ (Z Z' : GalileanAlgebra) : (Z - Z').γ = Z.γ - Z'.γ := rfl
@[simp] lemma sub_ε (Z Z' : GalileanAlgebra) : (Z - Z').ε = Z.ε - Z'.ε := rfl
@[simp] lemma real_smul_ω (c : ℝ) (Z : GalileanAlgebra) : (c • Z).ω = c • Z.ω := rfl
@[simp] lemma real_smul_β (c : ℝ) (Z : GalileanAlgebra) : (c • Z).β = c • Z.β := rfl
@[simp] lemma real_smul_γ (c : ℝ) (Z : GalileanAlgebra) : (c • Z).γ = c • Z.γ := rfl
@[simp] lemma real_smul_ε (c : ℝ) (Z : GalileanAlgebra) : (c • Z).ε = c • Z.ε := rfl

instance : Bracket GalileanAlgebra GalileanAlgebra := ⟨bracket⟩

/-- The Lie bracket of the Galilean Lie algebra is Souriau's bracket `GalileanAlgebra.bracket`. -/
lemma lie_def (Z Z' : GalileanAlgebra) : ⁅Z, Z'⁆ = bracket Z Z' := rfl

/-- Souriau's bracket makes the Galilean Lie algebra a Lie ring. -/
instance instLieRing : LieRing GalileanAlgebra where
  add_lie Z Z' W := by
    apply GalileanAlgebra.ext
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · simp [lie_def, bracket]
  lie_add Z Z' W := by
    apply GalileanAlgebra.ext
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail]
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · simp [lie_def, bracket]
  lie_self Z := by
    apply GalileanAlgebra.ext
    · simp [lie_def, bracket]
    · simp [lie_def, bracket]
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply]
    · simp [lie_def, bracket]
  leibniz_lie X Y Z := by
    apply GalileanAlgebra.ext
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · simp [lie_def, bracket]

/-- The Galilean Lie algebra is a real Lie algebra. -/
instance instLieAlgebra : LieAlgebra ℝ GalileanAlgebra where
  lie_smul c Z Z' := by
    apply GalileanAlgebra.ext
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail]
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · funext i
      fin_cases i <;> simp [lie_def, bracket, cross_apply, vecHead, vecTail] <;> ring
    · simp [lie_def, bracket]

/-!

## B. The real 2-cocycles and the mass cocycle

-/

/-- The real numbers as a trivial module of the Galilean Lie algebra, the coefficients of the
2-cocycles. -/
abbrev Coeff := TrivialLieModule ℝ GalileanAlgebra ℝ

/-- The pairing of a torsor with the Lie algebra, as a linear form. -/
def pairLinear (μ : GalileanTorsor) : GalileanAlgebra →ₗ[ℝ] ℝ where
  toFun := μ.pair
  map_add' Z Z' := by
    simp only [GalileanTorsor.pair, add_ω, add_β, add_γ, add_ε, dotProduct_add]
    ring
  map_smul' c Z := by
    simp only [GalileanTorsor.pair, real_smul_ω, real_smul_β, real_smul_γ, real_smul_ε,
      dotProduct_smul, smul_eq_mul, RingHom.id_apply]
    ring

/-- Souriau's 2-form `f₀` (12.130) as a real bilinear form. -/
def cocycleBilin : GalileanAlgebra →ₗ[ℝ] GalileanAlgebra →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ cocycle
    (fun Z Z' W => by simp only [cocycle, add_β, add_γ, add_dotProduct, dotProduct_add]; ring)
    (fun c Z W => by
      simp only [cocycle, real_smul_β, real_smul_γ, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      ring)
    (fun Z W W' => by simp only [cocycle, add_β, add_γ, add_dotProduct, dotProduct_add]; ring)
    (fun c Z W => by
      simp only [cocycle, real_smul_β, real_smul_γ, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      ring)

/-- `f₀` as a 2-cochain of the Galilean Lie algebra with real coefficients. -/
def massTwoCochain : twoCochain ℝ GalileanAlgebra Coeff :=
  ⟨cocycleBilin.compr₂ (TrivialLieModule.equiv ℝ GalileanAlgebra ℝ).symm.toLinearMap, fun Z => by
    simp [cocycleBilin, cocycle]⟩

/-- (12.129): `f₀` is a 2-cocycle of the Galilean Lie algebra with real coefficients. -/
def massTwoCocycle : twoCocycle ℝ GalileanAlgebra Coeff :=
  ⟨massTwoCochain, by
    rw [mem_twoCocycle_iff_of_trivial]
    intro X Y Z
    change cocycle X (bracket Y Z) = cocycle (bracket X Y) Z + cocycle Y (bracket X Z)
    simp only [cocycle, bracket, vec3_dotProduct, cross_apply]
    simp [vecHead, vecTail]
    ring⟩

/-!

## C. The computation

-/

/-- The properties of a real 2-cocycle `f` of the Galilean Lie algebra that the computation uses:
linearity in the first argument, antisymmetry, and the cyclic identity (11.33). -/
private structure IsCocycleFun (f : GalileanAlgebra → GalileanAlgebra → ℝ) : Prop where
  add_left : ∀ Z Z' W : GalileanAlgebra, f (Z + Z') W = f Z W + f Z' W
  smul_left : ∀ (c : ℝ) (Z W : GalileanAlgebra), f (c • Z) W = c * f Z W
  antisymm : ∀ Z Z' : GalileanAlgebra, f Z Z' = -f Z' Z
  cyclic : ∀ Z Z' Z'' : GalileanAlgebra,
    f Z (bracket Z' Z'') + f Z' (bracket Z'' Z) + f Z'' (bracket Z Z') = 0

/-- The form `μ₀[Z, Z'] + m f₀(Z)(Z')` of (12.133). -/
private def standardFun (μ₀ : GalileanTorsor) (m : ℝ) (Z Z' : GalileanAlgebra) : ℝ :=
  μ₀.pair (bracket Z Z') + m * cocycle Z Z'

/-- A cocycle vanishes when its first argument is zero. -/
private lemma aux_cocycle_zero_left {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (W : GalileanAlgebra) : f 0 W = 0 := by
  have h := hf.add_left 0 0 W
  have h0 : (0 : GalileanAlgebra) + 0 = 0 := by
    apply GalileanAlgebra.ext <;> simp
  rw [h0] at h
  linarith

/-- A cocycle vanishes when its second argument is zero. -/
private lemma aux_cocycle_zero_right {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (W : GalileanAlgebra) :
    f W 0 = 0 := by
  rw [hf.antisymm, aux_cocycle_zero_left hf, neg_zero]

/-- Additivity in the second argument. -/
private lemma aux_cocycle_add_right {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (W Z Z' : GalileanAlgebra) :
    f W (Z + Z') = f W Z + f W Z' := by
  rw [hf.antisymm, hf.add_left, hf.antisymm Z W, hf.antisymm Z' W]
  ring

/-- Homogeneity in the second argument. -/
private lemma aux_cocycle_smul_right {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (c : ℝ) (W Z : GalileanAlgebra) :
    f W (c • Z) = c * f W Z := by
  rw [hf.antisymm, hf.smul_left, hf.antisymm Z W]
  ring

/-- Brackets of the generators: rotation `R ω`, change of velocity `B β`, space translation
`T γ`, time translation `H`. -/
private lemma aux_br_T_H (γ : ℝ³) : bracket ⟨0, 0, γ, 0⟩ ⟨0, 0, 0, 1⟩ = 0 := by
  apply GalileanAlgebra.ext <;> simp [bracket, zero_ω, zero_β, zero_γ, zero_ε]

private lemma aux_br_H_B (β : ℝ³) : bracket ⟨0, 0, 0, 1⟩ ⟨0, β, 0, 0⟩ = ⟨0, 0, β, 0⟩ := by
  apply GalileanAlgebra.ext <;> simp [bracket]

private lemma aux_br_B_T (β γ : ℝ³) : bracket ⟨0, β, 0, 0⟩ ⟨0, 0, γ, 0⟩ = 0 := by
  apply GalileanAlgebra.ext <;> simp [bracket, zero_ω, zero_β, zero_γ, zero_ε]

private lemma aux_br_T_R (γ ω : ℝ³) : bracket ⟨0, 0, γ, 0⟩ ⟨ω, 0, 0, 0⟩ = ⟨0, 0, ω ⨯₃ γ, 0⟩ := by
  apply GalileanAlgebra.ext <;> simp [bracket]

private lemma aux_br_R_H (ω : ℝ³) : bracket ⟨ω, 0, 0, 0⟩ ⟨0, 0, 0, 1⟩ = 0 := by
  apply GalileanAlgebra.ext <;> simp [bracket, zero_ω, zero_β, zero_γ, zero_ε]

private lemma aux_br_H_T (γ : ℝ³) : bracket ⟨0, 0, 0, 1⟩ ⟨0, 0, γ, 0⟩ = 0 := by
  apply GalileanAlgebra.ext <;> simp [bracket, zero_ω, zero_β, zero_γ, zero_ε]

private lemma aux_br_R_R (ω ω' : ℝ³) : bracket ⟨ω, 0, 0, 0⟩ ⟨ω', 0, 0, 0⟩ = ⟨ω' ⨯₃ ω, 0, 0, 0⟩ := by
  apply GalileanAlgebra.ext <;> simp [bracket]

private lemma aux_br_H_R (ω : ℝ³) : bracket ⟨0, 0, 0, 1⟩ ⟨ω, 0, 0, 0⟩ = 0 := by
  apply GalileanAlgebra.ext <;> simp [bracket, zero_ω, zero_β, zero_γ, zero_ε]

/-- Every vector of `ℝ³` is a sum of three cross products. -/
private lemma aux_vec_eq_cross_sum (v : ℝ³) :
    v = ![0, 1, 0] ⨯₃ (v 0 • ![0, 0, 1]) + ![0, 0, 1] ⨯₃ (v 1 • ![1, 0, 0]) + ![1, 0, 0] ⨯₃
    (v 2 • ![0, 1, 0]) := by
  funext i
  fin_cases i <;> simp [cross_apply]

private lemma aux_T_add (a b : ℝ³) : (⟨0, 0, a + b, 0⟩ : GalileanAlgebra) =
    ⟨0, 0, a, 0⟩ + ⟨0, 0, b, 0⟩ := by
  apply GalileanAlgebra.ext <;> simp [add_ω, add_β, add_γ, add_ε]

private lemma aux_R_add (a b : ℝ³) : (⟨a + b, 0, 0, 0⟩ : GalileanAlgebra) =
    ⟨a, 0, 0, 0⟩ + ⟨b, 0, 0, 0⟩ := by
  apply GalileanAlgebra.ext <;> simp [add_ω, add_β, add_γ, add_ε]

private lemma aux_R_decomp (a : ℝ³) : (⟨a, 0, 0, 0⟩ : GalileanAlgebra) =
    a 0 • (⟨![1, 0, 0], 0, 0, 0⟩ : GalileanAlgebra) + a 1 • ⟨![0, 1, 0], 0, 0, 0⟩ + a 2 •
    ⟨![0, 0, 1], 0, 0, 0⟩ := by
  apply GalileanAlgebra.ext
  · funext i
    fin_cases i <;> simp [add_ω, real_smul_ω]
  · simp [add_β, real_smul_β]
  · simp [add_γ, real_smul_γ]
  · simp [add_ε, real_smul_ε]

private lemma aux_B_decomp (a : ℝ³) : (⟨0, a, 0, 0⟩ : GalileanAlgebra) =
    a 0 • (⟨0, ![1, 0, 0], 0, 0⟩ : GalileanAlgebra) + a 1 • ⟨0, ![0, 1, 0], 0, 0⟩ + a 2 •
    ⟨0, ![0, 0, 1], 0, 0⟩ := by
  apply GalileanAlgebra.ext
  · simp [add_ω, real_smul_ω]
  · funext i
    fin_cases i <;> simp [add_β, real_smul_β]
  · simp [add_γ, real_smul_γ]
  · simp [add_ε, real_smul_ε]

private lemma aux_T_decomp (a : ℝ³) : (⟨0, 0, a, 0⟩ : GalileanAlgebra) =
    a 0 • (⟨0, 0, ![1, 0, 0], 0⟩ : GalileanAlgebra) + a 1 • ⟨0, 0, ![0, 1, 0], 0⟩ + a 2 •
    ⟨0, 0, ![0, 0, 1], 0⟩ := by
  apply GalileanAlgebra.ext
  · simp [add_ω, real_smul_ω]
  · simp [add_β, real_smul_β]
  · funext i
    fin_cases i <;> simp [add_γ, real_smul_γ]
  · simp [add_ε, real_smul_ε]

private lemma aux_expand_left3 {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (a : ℝ³) (X0 X1 X2 W : GalileanAlgebra) :
    f (a 0 • X0 + a 1 • X1 + a 2 • X2) W = a 0 * f X0 W + a 1 * f X1 W + a 2 * f X2 W := by
  simp only [hf.add_left, hf.smul_left]

private lemma aux_expand_right3 {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (b : ℝ³) (W Y0 Y1 Y2 : GalileanAlgebra) :
    f W (b 0 • Y0 + b 1 • Y1 + b 2 • Y2) = b 0 * f W Y0 + b 1 * f W Y1 + b 2 * f W Y2 := by
  simp only [aux_cocycle_add_right hf, aux_cocycle_smul_right hf]

private lemma aux_br_B_B (β β' : ℝ³) : bracket ⟨0, β, 0, 0⟩ ⟨0, β', 0, 0⟩ = 0 := by
  apply GalileanAlgebra.ext <;> simp [bracket, zero_ω, zero_β, zero_γ, zero_ε]

private lemma aux_br_B_R (β ω : ℝ³) : bracket ⟨0, β, 0, 0⟩ ⟨ω, 0, 0, 0⟩ = ⟨0, ω ⨯₃ β, 0, 0⟩ := by
  apply GalileanAlgebra.ext <;> simp [bracket]

private lemma aux_br_R_B (ω β : ℝ³) : bracket ⟨ω, 0, 0, 0⟩ ⟨0, β, 0, 0⟩ =
    (-1 : ℝ) • ⟨0, ω ⨯₃ β, 0, 0⟩ := by
  apply GalileanAlgebra.ext <;> simp [bracket]

private lemma aux_br_B_H (β : ℝ³) : bracket ⟨0, β, 0, 0⟩ ⟨0, 0, 0, 1⟩ =
    (-1 : ℝ) • ⟨0, 0, β, 0⟩ := by
  apply GalileanAlgebra.ext <;> simp [bracket]

/-- Rotation-rotation block: `f(R a)(R b) = l ⬝ (b × a)`. -/
private lemma aux_blk_RR {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (a b : ℝ³) :
    f ⟨a, 0, 0, 0⟩ ⟨b, 0, 0, 0⟩ = ![f ⟨![0, 0, 1], 0, 0, 0⟩ ⟨![0, 1, 0], 0, 0, 0⟩,
      f ⟨![1, 0, 0], 0, 0, 0⟩ ⟨![0, 0, 1], 0, 0, 0⟩,
      f ⟨![0, 1, 0], 0, 0, 0⟩ ⟨![1, 0, 0], 0, 0, 0⟩] ⬝ᵥ (b ⨯₃ a) := by
  have a12 := hf.antisymm ⟨![0, 1, 0], 0, 0, 0⟩ ⟨![0, 0, 1], 0, 0, 0⟩
  have a20 := hf.antisymm ⟨![0, 0, 1], 0, 0, 0⟩ ⟨![1, 0, 0], 0, 0, 0⟩
  have a01 := hf.antisymm ⟨![1, 0, 0], 0, 0, 0⟩ ⟨![0, 1, 0], 0, 0, 0⟩
  have d0 : f ⟨![1, 0, 0], 0, 0, 0⟩ ⟨![1, 0, 0], 0, 0, 0⟩ = 0 := by
    linarith [hf.antisymm ⟨![1, 0, 0], 0, 0, 0⟩ ⟨![1, 0, 0], 0, 0, 0⟩]
  have d1 : f ⟨![0, 1, 0], 0, 0, 0⟩ ⟨![0, 1, 0], 0, 0, 0⟩ = 0 := by
    linarith [hf.antisymm ⟨![0, 1, 0], 0, 0, 0⟩ ⟨![0, 1, 0], 0, 0, 0⟩]
  have d2 : f ⟨![0, 0, 1], 0, 0, 0⟩ ⟨![0, 0, 1], 0, 0, 0⟩ = 0 := by
    linarith [hf.antisymm ⟨![0, 0, 1], 0, 0, 0⟩ ⟨![0, 0, 1], 0, 0, 0⟩]
  rw [aux_R_decomp a, aux_R_decomp b, aux_expand_left3 hf, aux_expand_right3 hf,
      aux_expand_right3 hf, aux_expand_right3 hf,
    a12, a20, a01, d0, d1, d2]
  simp [dotProduct, Fin.sum_univ_three, cross_apply]
  ring

/-- Rotation-velocity block: `f(R a)(B b) = g ⬝ (a × b)`. -/
private lemma aux_blk_RB {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (a b : ℝ³) :
    f ⟨a, 0, 0, 0⟩ ⟨0, b, 0, 0⟩ = ![f ⟨![0, 1, 0], 0, 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩,
      f ⟨![0, 0, 1], 0, 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩,
      f ⟨![1, 0, 0], 0, 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩] ⬝ᵥ (a ⨯₃ b) := by
  have rel : ∀ w w' c : ℝ³, -f ⟨w, 0, 0, 0⟩ ⟨0, w' ⨯₃ c, 0, 0⟩ + f ⟨w', 0, 0, 0⟩ ⟨0, w ⨯₃ c, 0, 0⟩
      - f ⟨w' ⨯₃ w, 0, 0, 0⟩ ⟨0, c, 0, 0⟩ = 0 := by
    intro w w' c
    have h := hf.cyclic ⟨w, 0, 0, 0⟩ ⟨w', 0, 0, 0⟩ ⟨0, c, 0, 0⟩
    rw [aux_br_R_B, aux_br_B_R, aux_br_R_R, aux_cocycle_smul_right hf,
        hf.antisymm ⟨0, c, 0, 0⟩ ⟨w' ⨯₃ w, 0, 0, 0⟩] at h
    linarith
  have r1 := rel ![1, 0, 0] ![0, 1, 0] ![0, 1, 0]
  have r2 := rel ![0, 1, 0] ![0, 0, 1] ![0, 0, 1]
  have r3 := rel ![0, 0, 1] ![1, 0, 0] ![1, 0, 0]
  have r4 := rel ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]
  have r5 := rel ![0, 1, 0] ![0, 0, 1] ![1, 0, 0]
  have r6 := rel ![0, 0, 1] ![1, 0, 0] ![0, 1, 0]
  rw [aux_B_decomp (![0, 1, 0] ⨯₃ ![0, 1, 0]), aux_B_decomp (![1, 0, 0] ⨯₃ ![0, 1, 0]),
    aux_R_decomp (![0, 1, 0] ⨯₃ ![1, 0, 0]), aux_expand_right3 hf, aux_expand_right3 hf,
    aux_expand_left3 hf] at r1
  rw [aux_B_decomp (![0, 0, 1] ⨯₃ ![0, 0, 1]), aux_B_decomp (![0, 1, 0] ⨯₃ ![0, 0, 1]),
    aux_R_decomp (![0, 0, 1] ⨯₃ ![0, 1, 0]), aux_expand_right3 hf, aux_expand_right3 hf,
    aux_expand_left3 hf] at r2
  rw [aux_B_decomp (![1, 0, 0] ⨯₃ ![1, 0, 0]), aux_B_decomp (![0, 0, 1] ⨯₃ ![1, 0, 0]),
    aux_R_decomp (![1, 0, 0] ⨯₃ ![0, 0, 1]), aux_expand_right3 hf, aux_expand_right3 hf,
    aux_expand_left3 hf] at r3
  rw [aux_B_decomp (![0, 1, 0] ⨯₃ ![0, 0, 1]), aux_B_decomp (![1, 0, 0] ⨯₃ ![0, 0, 1]),
    aux_R_decomp (![0, 1, 0] ⨯₃ ![1, 0, 0]), aux_expand_right3 hf, aux_expand_right3 hf,
    aux_expand_left3 hf] at r4
  rw [aux_B_decomp (![0, 0, 1] ⨯₃ ![1, 0, 0]), aux_B_decomp (![0, 1, 0] ⨯₃ ![1, 0, 0]),
    aux_R_decomp (![0, 0, 1] ⨯₃ ![0, 1, 0]), aux_expand_right3 hf, aux_expand_right3 hf,
    aux_expand_left3 hf] at r5
  rw [aux_B_decomp (![1, 0, 0] ⨯₃ ![0, 1, 0]), aux_B_decomp (![0, 0, 1] ⨯₃ ![0, 1, 0]),
    aux_R_decomp (![1, 0, 0] ⨯₃ ![0, 0, 1]), aux_expand_right3 hf, aux_expand_right3 hf,
    aux_expand_left3 hf] at r6
  simp [cross_apply] at r1 r2 r3 r4 r5 r6
  have e00 : f ⟨![1, 0, 0], 0, 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩ = 0 := by linarith
  have e11 : f ⟨![0, 1, 0], 0, 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩ = 0 := by linarith
  have e22 : f ⟨![0, 0, 1], 0, 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩ = 0 := by linarith
  have e21 : f ⟨![0, 0, 1], 0, 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩ =
      -f ⟨![0, 1, 0], 0, 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩ := by
    linarith
  have e02 : f ⟨![1, 0, 0], 0, 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩ =
      -f ⟨![0, 0, 1], 0, 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩ := by
    linarith
  have e10 : f ⟨![0, 1, 0], 0, 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩ =
      -f ⟨![1, 0, 0], 0, 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩ := by
    linarith
  rw [aux_R_decomp a, aux_B_decomp b, aux_expand_left3 hf, aux_expand_right3 hf,
      aux_expand_right3 hf, aux_expand_right3 hf,
    e00, e11, e22, e21, e02, e10]
  simp [dotProduct, Fin.sum_univ_three, cross_apply]
  ring

/-- Time-velocity block: `f(H)(B b) = p ⬝ b`. -/
private lemma aux_blk_HB {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (b : ℝ³) :
    f ⟨0, 0, 0, 1⟩ ⟨0, b, 0, 0⟩ =
    ![f ⟨0, 0, 0, 1⟩ ⟨0, ![1, 0, 0], 0, 0⟩, f ⟨0, 0, 0, 1⟩ ⟨0, ![0, 1, 0], 0, 0⟩,
      f ⟨0, 0, 0, 1⟩ ⟨0, ![0, 0, 1], 0, 0⟩] ⬝ᵥ b := by
  rw [aux_B_decomp b, aux_expand_right3 hf]
  simp [dotProduct, Fin.sum_univ_three]
  ring

/-- Rotation-translation block: `f(R a)(T c) = -(p ⬝ (a × c))`. -/
private lemma aux_blk_RT {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (a c : ℝ³) :
    f ⟨a, 0, 0, 0⟩ ⟨0, 0, c, 0⟩ =
    -(![f ⟨0, 0, 0, 1⟩ ⟨0, ![1, 0, 0], 0, 0⟩, f ⟨0, 0, 0, 1⟩ ⟨0, ![0, 1, 0], 0, 0⟩,
      f ⟨0, 0, 0, 1⟩ ⟨0, ![0, 0, 1], 0, 0⟩] ⬝ᵥ (a ⨯₃ c)) := by
  have h := hf.cyclic ⟨a, 0, 0, 0⟩ ⟨0, c, 0, 0⟩ ⟨0, 0, 0, 1⟩
  rw [aux_br_B_H, aux_br_H_R, aux_br_R_B, aux_cocycle_smul_right hf, aux_cocycle_smul_right hf,
      aux_cocycle_zero_right hf,
    aux_blk_HB hf] at h
  linarith

/-- An element of the algebra is the sum of its four parts. -/
private lemma aux_Z_decomp (Z : GalileanAlgebra) : Z = ⟨Z.ω, 0, 0, 0⟩ + ⟨0, Z.β, 0, 0⟩ +
    ⟨0, 0, Z.γ, 0⟩ + Z.ε • (⟨0, 0, 0, 1⟩ : GalileanAlgebra) := by
  apply GalileanAlgebra.ext <;> simp [add_ω, add_β, add_γ, add_ε, real_smul_ω, real_smul_β,
      real_smul_γ, real_smul_ε]


/-- No term between two space translations: `f(T γ)(T γ') = 0`. -/
private lemma block_translation_translation {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (γ γ' : ℝ³) :
    f ⟨0, 0, γ, 0⟩ ⟨0, 0, γ', 0⟩ = 0 := by
  have h := hf.cyclic ⟨0, γ', 0, 0⟩ ⟨0, 0, γ, 0⟩ ⟨0, 0, 0, 1⟩
  rw [aux_br_T_H, aux_br_H_B, aux_br_B_T, aux_cocycle_zero_right hf, aux_cocycle_zero_right hf] at h
  linarith


/-- No term between two changes of velocity: `f(B β)(B β') = 0`. -/
private lemma block_boost_boost {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (β β' : ℝ³) :
    f ⟨0, β, 0, 0⟩ ⟨0, β', 0, 0⟩ = 0 := by
  have rel : ∀ b b' w : ℝ³, f ⟨0, b, 0, 0⟩ ⟨0, w ⨯₃ b', 0, 0⟩ =
      f ⟨0, b', 0, 0⟩ ⟨0, w ⨯₃ b, 0, 0⟩ := by
    intro b b' w
    have h := hf.cyclic ⟨w, 0, 0, 0⟩ ⟨0, b, 0, 0⟩ ⟨0, b', 0, 0⟩
    rw [aux_br_B_B, aux_br_B_R, aux_br_R_B, aux_cocycle_zero_right hf,
        aux_cocycle_smul_right hf] at h
    linarith
  have r1 := rel ![1, 0, 0] ![0, 0, 1] ![1, 0, 0]
  have r2 := rel ![0, 1, 0] ![1, 0, 0] ![0, 1, 0]
  have r3 := rel ![0, 0, 1] ![0, 1, 0] ![0, 0, 1]
  rw [aux_B_decomp (![1, 0, 0] ⨯₃ ![0, 0, 1]), aux_B_decomp (![1, 0, 0] ⨯₃ ![1, 0, 0]),
      aux_expand_right3 hf,
    aux_expand_right3 hf] at r1
  rw [aux_B_decomp (![0, 1, 0] ⨯₃ ![1, 0, 0]), aux_B_decomp (![0, 1, 0] ⨯₃ ![0, 1, 0]),
      aux_expand_right3 hf,
    aux_expand_right3 hf] at r2
  rw [aux_B_decomp (![0, 0, 1] ⨯₃ ![0, 1, 0]), aux_B_decomp (![0, 0, 1] ⨯₃ ![0, 0, 1]),
      aux_expand_right3 hf,
    aux_expand_right3 hf] at r3
  simp [cross_apply] at r1 r2 r3
  have a01 := hf.antisymm ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩
  have a12 := hf.antisymm ⟨0, ![0, 1, 0], 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩
  have a20 := hf.antisymm ⟨0, ![0, 0, 1], 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩
  have d0 := hf.antisymm ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩
  have d1 := hf.antisymm ⟨0, ![0, 1, 0], 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩
  have d2 := hf.antisymm ⟨0, ![0, 0, 1], 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩
  rw [aux_B_decomp β, aux_B_decomp β', aux_expand_left3 hf, aux_expand_right3 hf,
      aux_expand_right3 hf, aux_expand_right3 hf]
  have e01 : f ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩ = 0 := by linarith
  have e12 : f ⟨0, ![0, 1, 0], 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩ = 0 := by linarith
  have e20 : f ⟨0, ![0, 0, 1], 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩ = 0 := by linarith
  have e10 : f ⟨0, ![0, 1, 0], 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩ = 0 := by linarith
  have e21 : f ⟨0, ![0, 0, 1], 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩ = 0 := by linarith
  have e02 : f ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩ = 0 := by linarith
  have e00 : f ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩ = 0 := by linarith
  have e11 : f ⟨0, ![0, 1, 0], 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩ = 0 := by linarith
  have e22 : f ⟨0, ![0, 0, 1], 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩ = 0 := by linarith
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  ring


/-- No term between the time translation and a space translation: `f(H)(T γ) = 0`. -/
private lemma block_time_translation {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (γ : ℝ³) :
    f ⟨0, 0, 0, 1⟩ ⟨0, 0, γ, 0⟩ = 0 := by
  have key : ∀ ω γ₀ : ℝ³, f ⟨0, 0, 0, 1⟩ ⟨0, 0, ω ⨯₃ γ₀, 0⟩ = 0 := by
    intro ω γ₀
    have h := hf.cyclic ⟨0, 0, 0, 1⟩ ⟨0, 0, γ₀, 0⟩ ⟨ω, 0, 0, 0⟩
    rw [aux_br_T_R, aux_br_R_H, aux_br_H_T, aux_cocycle_zero_right hf,
        aux_cocycle_zero_right hf] at h
    linarith
  rw [aux_vec_eq_cross_sum γ, aux_T_add, aux_T_add, aux_cocycle_add_right hf,
      aux_cocycle_add_right hf, key, key, key]
  ring


/-- No term between a rotation and the time translation: `f(R ω)(H) = 0`. -/
private lemma block_rotation_time {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (ω : ℝ³) :
    f ⟨ω, 0, 0, 0⟩ ⟨0, 0, 0, 1⟩ = 0 := by
  have key : ∀ a b : ℝ³, f ⟨0, 0, 0, 1⟩ ⟨a ⨯₃ b, 0, 0, 0⟩ = 0 := by
    intro a b
    have h := hf.cyclic ⟨0, 0, 0, 1⟩ ⟨b, 0, 0, 0⟩ ⟨a, 0, 0, 0⟩
    rw [aux_br_R_R, aux_br_R_H, aux_br_H_R, aux_cocycle_zero_right hf,
        aux_cocycle_zero_right hf] at h
    linarith
  rw [hf.antisymm, aux_vec_eq_cross_sum ω, aux_R_add, aux_R_add, aux_cocycle_add_right hf,
      aux_cocycle_add_right hf, key, key, key]
  ring


/-- Between a change of velocity and a space translation the term is isotropic:
`f(B β)(T γ) = ⟨β, γ⟩ f(B e₁)(T e₁)`. -/
private lemma block_boost_translation {f : GalileanAlgebra → GalileanAlgebra → ℝ}
    (hf : IsCocycleFun f) (β γ : ℝ³) :
    f ⟨0, β, 0, 0⟩ ⟨0, 0, γ, 0⟩ = (β ⬝ᵥ γ) * f ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩ := by
  have sym : ∀ b b' : ℝ³, f ⟨0, b', 0, 0⟩ ⟨0, 0, b, 0⟩ = f ⟨0, b, 0, 0⟩ ⟨0, 0, b', 0⟩ := by
    intro b b'
    have h := hf.cyclic ⟨0, b, 0, 0⟩ ⟨0, b', 0, 0⟩ ⟨0, 0, 0, 1⟩
    rw [aux_br_B_H, aux_br_H_B, aux_br_B_B, aux_cocycle_zero_right hf,
        aux_cocycle_smul_right hf] at h
    linarith
  have inv : ∀ b c w : ℝ³, f ⟨0, b, 0, 0⟩ ⟨0, 0, w ⨯₃ c, 0⟩ + f ⟨0, w ⨯₃ b, 0, 0⟩ ⟨0, 0, c, 0⟩ =
      0 := by
    intro b c w
    have h := hf.cyclic ⟨w, 0, 0, 0⟩ ⟨0, b, 0, 0⟩ ⟨0, 0, c, 0⟩
    rw [aux_br_B_T, aux_br_T_R, aux_br_R_B, aux_cocycle_zero_right hf, aux_cocycle_smul_right hf,
      hf.antisymm ⟨0, 0, c, 0⟩ ⟨0, w ⨯₃ b, 0, 0⟩] at h
    linarith
  have s01 := sym ![1, 0, 0] ![0, 1, 0]
  have s12 := sym ![0, 1, 0] ![0, 0, 1]
  have s20 := sym ![0, 0, 1] ![1, 0, 0]
  have ia := inv ![1, 0, 0] ![1, 0, 0] ![0, 0, 1]
  have ib := inv ![0, 1, 0] ![0, 1, 0] ![1, 0, 0]
  have ic := inv ![0, 0, 1] ![0, 0, 1] ![0, 1, 0]
  have id := inv ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]
  have ie := inv ![0, 1, 0] ![0, 0, 1] ![1, 0, 0]
  rw [aux_T_decomp (![0, 0, 1] ⨯₃ ![1, 0, 0]), aux_B_decomp (![0, 0, 1] ⨯₃ ![1, 0, 0]),
      aux_expand_right3 hf,
    aux_expand_left3 hf] at ia
  rw [aux_T_decomp (![1, 0, 0] ⨯₃ ![0, 1, 0]), aux_B_decomp (![1, 0, 0] ⨯₃ ![0, 1, 0]),
      aux_expand_right3 hf,
    aux_expand_left3 hf] at ib
  rw [aux_T_decomp (![0, 1, 0] ⨯₃ ![0, 0, 1]), aux_B_decomp (![0, 1, 0] ⨯₃ ![0, 0, 1]),
      aux_expand_right3 hf,
    aux_expand_left3 hf] at ic
  rw [aux_T_decomp (![0, 0, 1] ⨯₃ ![0, 1, 0]), aux_B_decomp (![0, 0, 1] ⨯₃ ![1, 0, 0]),
      aux_expand_right3 hf,
    aux_expand_left3 hf] at id
  rw [aux_T_decomp (![1, 0, 0] ⨯₃ ![0, 0, 1]), aux_B_decomp (![1, 0, 0] ⨯₃ ![0, 1, 0]),
      aux_expand_right3 hf,
    aux_expand_left3 hf] at ie
  simp [cross_apply] at ia ib ic id ie
  have e01 : f ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![0, 1, 0], 0⟩ = 0 := by linarith
  have e10 : f ⟨0, ![0, 1, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩ = 0 := by linarith
  have e12 : f ⟨0, ![0, 1, 0], 0, 0⟩ ⟨0, 0, ![0, 0, 1], 0⟩ = 0 := by linarith
  have e21 : f ⟨0, ![0, 0, 1], 0, 0⟩ ⟨0, 0, ![0, 1, 0], 0⟩ = 0 := by linarith
  have e20 : f ⟨0, ![0, 0, 1], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩ = 0 := by linarith
  have e02 : f ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![0, 0, 1], 0⟩ = 0 := by linarith
  have e11 : f ⟨0, ![0, 1, 0], 0, 0⟩ ⟨0, 0, ![0, 1, 0], 0⟩ =
      f ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩ := by
    linarith
  have e22 : f ⟨0, ![0, 0, 1], 0, 0⟩ ⟨0, 0, ![0, 0, 1], 0⟩ =
      f ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩ := by
    linarith
  rw [aux_B_decomp β, aux_T_decomp γ, aux_expand_left3 hf, aux_expand_right3 hf,
      aux_expand_right3 hf, aux_expand_right3 hf,
    e01, e10, e12, e21, e20, e02, e11, e22]
  simp only [dotProduct, Fin.sum_univ_three]
  ring


/-- Every function with the properties of `IsCocycleFun` is `μ₀[Z, Z'] + m f₀(Z)(Z')` for a
torsor `μ₀` and a number `m`. -/
private lemma block_eq_standard {f : GalileanAlgebra → GalileanAlgebra → ℝ} (hf : IsCocycleFun f) :
    ∃ (μ₀ : GalileanTorsor) (m : ℝ), f = standardFun μ₀ m := by
  refine ⟨⟨![f ⟨![0, 0, 1], 0, 0, 0⟩ ⟨![0, 1, 0], 0, 0, 0⟩,
      f ⟨![1, 0, 0], 0, 0, 0⟩ ⟨![0, 0, 1], 0, 0, 0⟩,
      f ⟨![0, 1, 0], 0, 0, 0⟩ ⟨![1, 0, 0], 0, 0, 0⟩],
    ![f ⟨![0, 1, 0], 0, 0, 0⟩ ⟨0, ![0, 0, 1], 0, 0⟩, f ⟨![0, 0, 1], 0, 0, 0⟩ ⟨0, ![1, 0, 0], 0, 0⟩,
      f ⟨![1, 0, 0], 0, 0, 0⟩ ⟨0, ![0, 1, 0], 0, 0⟩],
    ![f ⟨0, 0, 0, 1⟩ ⟨0, ![1, 0, 0], 0, 0⟩, f ⟨0, 0, 0, 1⟩ ⟨0, ![0, 1, 0], 0, 0⟩,
      f ⟨0, 0, 0, 1⟩ ⟨0, ![0, 0, 1], 0, 0⟩], 0⟩,
    f ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩, ?_⟩
  funext Z Z'
  have hH : f ⟨0, 0, 0, 1⟩ ⟨0, 0, 0, 1⟩ = 0 := by linarith [hf.antisymm ⟨0, 0, 0, 1⟩ ⟨0, 0, 0, 1⟩]
  conv_lhs => rw [aux_Z_decomp Z, aux_Z_decomp Z']
  simp only [hf.add_left, hf.smul_left, aux_cocycle_add_right hf, aux_cocycle_smul_right hf]
  rw [aux_blk_RR hf Z.ω Z'.ω, aux_blk_RB hf Z.ω Z'.β, aux_blk_RT hf Z.ω Z'.γ,
      block_rotation_time hf Z.ω,
    hf.antisymm ⟨0, Z.β, 0, 0⟩ ⟨Z'.ω, 0, 0, 0⟩, aux_blk_RB hf Z'.ω Z.β,
    block_boost_boost hf Z.β Z'.β,
    block_boost_translation hf Z.β Z'.γ, hf.antisymm ⟨0, Z.β, 0, 0⟩ ⟨0, 0, 0, 1⟩, aux_blk_HB hf Z.β,
    hf.antisymm ⟨0, 0, Z.γ, 0⟩ ⟨Z'.ω, 0, 0, 0⟩, aux_blk_RT hf Z'.ω Z.γ,
    hf.antisymm ⟨0, 0, Z.γ, 0⟩ ⟨0, Z'.β, 0, 0⟩, block_boost_translation hf Z'.β Z.γ,
    block_translation_translation hf Z.γ Z'.γ, hf.antisymm ⟨0, 0, Z.γ, 0⟩ ⟨0, 0, 0, 1⟩,
    block_time_translation hf Z.γ, hf.antisymm ⟨0, 0, 0, 1⟩ ⟨Z'.ω, 0, 0, 0⟩,
    block_rotation_time hf Z'.ω,
    aux_blk_HB hf Z'.β, block_time_translation hf Z'.γ, hH]
  simp [standardFun, GalileanTorsor.pair, bracket, cocycle, dotProduct, Fin.sum_univ_three,
      cross_apply, Matrix.vecHead,
    Matrix.vecTail, Pi.smul_apply, smul_eq_mul]
  ring

/-- The value of `μ₀[Z, Z'] + m f₀(Z)(Z')` on a change of velocity and a space translation along the
first axis is `m`. -/
private lemma standardFun_boost_translation (μ₀ : GalileanTorsor) (m : ℝ) :
    standardFun μ₀ m ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩ = m := by
  simp [standardFun, cocycle, GalileanTorsor.pair, bracket]

/-!

## D. Every real 2-cocycle is a coboundary plus a multiple of `f₀`

-/

/-- A real 2-cocycle, read as a function of two variables, has the properties used in the
computation. -/
private lemma isCocycleFun_of_twoCocycle (c : twoCocycle ℝ GalileanAlgebra Coeff) :
    IsCocycleFun (fun Z Z' => TrivialLieModule.equiv ℝ GalileanAlgebra ℝ (c.1 Z Z')) where
  add_left Z Z' W := by
    simp only [map_add, LinearMap.add_apply]
  smul_left a Z W := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  antisymm Z Z' := by
    rw [← twoCochain_skew c.1 Z' Z, map_neg]
  cyclic Z Z' Z'' := by
    have h := (mem_twoCocycle_iff_of_trivial ℝ GalileanAlgebra Coeff c.1).mp c.2 Z Z' Z''
    have h1 : c.1 ⁅Z, Z'⁆ Z'' = -c.1 Z'' ⁅Z, Z'⁆ := by rw [twoCochain_skew]
    have h2 : c.1 Z' ⁅Z, Z''⁆ = -c.1 Z' ⁅Z'', Z⁆ := by rw [← lie_skew, map_neg]
    rw [h1, h2] at h
    have h' := congrArg (TrivialLieModule.equiv ℝ GalileanAlgebra ℝ) h
    simp only [map_add, map_neg] at h'
    simp only [← lie_def]
    linarith

/-- The mass of a real 2-cocycle `c` of the Galilean Lie algebra: its value `c(Z)(Z')` on a change
of velocity `Z = (0, e₁, 0, 0)` and a space translation `Z' = (0, 0, e₁, 0)` along the same axis.
For `f₀` it is `1` (`massOf_massTwoCocycle`). -/
def massOf : twoCocycle ℝ GalileanAlgebra Coeff →ₗ[ℝ] ℝ where
  toFun c := TrivialLieModule.equiv ℝ GalileanAlgebra ℝ
    (c.1 ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩)
  map_add' c c' := by
    simp only [Submodule.coe_add, add_apply_apply, map_add]
  map_smul' a c := by
    simp only [Submodule.coe_smul, smul_apply_apply, map_smul, RingHom.id_apply]

/-- The mass of `f₀` is `1`. -/
lemma massOf_massTwoCocycle : massOf massTwoCocycle = 1 := by
  change cocycle ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩ = 1
  exact cocycle_boost_translation

/-- (12.133) at the level of the algebra: every real 2-cocycle `c` of the Galilean Lie algebra is a
coboundary `d₁₂ φ` plus its mass times `f₀`. With Souriau's coboundaries `μ₀[Z, Z']` (p. 116,
note (1)), `φ = -μ₀`; Mathlib's `d₁₂` for trivial coefficients is `d₁₂ φ (Z, Z') = -φ([Z, Z'])`. -/
lemma twoCocycle_eq_d₁₂_add_smul (c : twoCocycle ℝ GalileanAlgebra Coeff) :
    ∃ φ : oneCochain ℝ GalileanAlgebra Coeff,
      c.1 = d₁₂ ℝ GalileanAlgebra Coeff φ + massOf c • massTwoCochain := by
  obtain ⟨μ₀, m, hf⟩ := block_eq_standard (isCocycleFun_of_twoCocycle c)
  have hm : massOf c = m := by
    have h := congrFun (congrFun hf ⟨0, ![1, 0, 0], 0, 0⟩) ⟨0, 0, ![1, 0, 0], 0⟩
    rw [standardFun_boost_translation] at h
    exact h
  refine ⟨(TrivialLieModule.equiv ℝ GalileanAlgebra ℝ).symm.toLinearMap ∘ₗ (-pairLinear μ₀), ?_⟩
  apply Subtype.ext
  refine LinearMap.ext fun Z => LinearMap.ext fun Z' => ?_
  have h := congrFun (congrFun hf Z) Z'
  change TrivialLieModule.equiv ℝ GalileanAlgebra ℝ (c.1 Z Z') = _ at h
  rw [hm]
  change c.1 Z Z' = d₁₂ ℝ GalileanAlgebra Coeff _ Z Z' + (m • massTwoCochain) Z Z'
  rw [d₁₂_apply_apply_ofTrivial, smul_apply_apply]
  apply (TrivialLieModule.equiv ℝ GalileanAlgebra ℝ).injective
  rw [h]
  change μ₀.pair (bracket Z Z') + m * cocycle Z Z' = -(-μ₀.pair ⁅Z, Z'⁆) + m * cocycle Z Z'
  rw [lie_def, neg_neg]

/-!

## E. The mass classifies the 2-cocycles up to coboundaries

-/

/-- The real 2-coboundaries `d₁₂ φ` of the Galilean Lie algebra, as a submodule of the
2-cocycles. -/
def twoCoboundary : Submodule ℝ (twoCocycle ℝ GalileanAlgebra Coeff) :=
  (LinearMap.range (d₁₂ ℝ GalileanAlgebra Coeff)).comap (twoCocycle ℝ GalileanAlgebra Coeff).subtype

/-- A real 2-cocycle is a coboundary if and only if its mass is zero. -/
lemma mem_twoCoboundary_iff (c : twoCocycle ℝ GalileanAlgebra Coeff) :
    c ∈ twoCoboundary ↔ massOf c = 0 := by
  constructor
  · rintro ⟨φ, hφ⟩
    have hc : c.1 = d₁₂ ℝ GalileanAlgebra Coeff φ := hφ.symm
    change TrivialLieModule.equiv ℝ GalileanAlgebra ℝ
      (c.1 ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩) = 0
    rw [hc, d₁₂_apply_apply_ofTrivial, lie_def, bracket_boost_translation, map_zero, neg_zero,
      map_zero]
  · intro h
    obtain ⟨φ, hφ⟩ := twoCocycle_eq_d₁₂_add_smul c
    rw [h, zero_smul, add_zero] at hφ
    exact ⟨φ, hφ.symm⟩

/-- `f₀` is not a coboundary. -/
lemma massTwoCocycle_not_mem_twoCoboundary : massTwoCocycle ∉ twoCoboundary := by
  rw [mem_twoCoboundary_iff, massOf_massTwoCocycle]
  exact one_ne_zero

/-- The mass of a real 2-cocycle vanishes exactly on the coboundaries. -/
lemma ker_massOf : LinearMap.ker massOf = twoCoboundary :=
  Submodule.ext fun c => by rw [LinearMap.mem_ker, mem_twoCoboundary_iff]

/-- Every real number is the mass of a real 2-cocycle, a multiple of `f₀`. -/
lemma massOf_surjective : Function.Surjective massOf := fun m =>
  ⟨m • massTwoCocycle, by rw [map_smul, massOf_massTwoCocycle, smul_eq_mul, mul_one]⟩

end GalileanAlgebra

end ClassicalMechanics
