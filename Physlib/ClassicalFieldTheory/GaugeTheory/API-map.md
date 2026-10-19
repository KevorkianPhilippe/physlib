# Gauge theory

## Abstract (Alpha)

A gauge theory is built around a structure group, a gauge field valued in its Lie algebra, the
curvature of that field, the gauge-covariant derivative acting on matter fields, and the gauge
transformations under which the curvature transforms covariantly and the action is invariant. Two
concrete pieces of this picture are in place: the abelian theory, realized through the
electromagnetic potential and the gauge invariance of its field strength, and the Standard Model
gauge group as a group with its central discrete subgroup; the general non-abelian theory, with its
connections, curvature and covariant derivatives, extends both.

## Content (Alpha)

### The abelian theory

In electromagnetism the gauge field is the electromagnetic potential {1}, a Lorentz-vector-valued
field on spacetime, and its field strength is built from that potential. [2][3] A gauge
transformation shifts the potential by the gradient of a scalar {2}, and the pure-gauge potential is
the shift of zero. [4] Gauge transformations leave the field strength invariant. [5] In particular a
pure-gauge potential has vanishing field strength, and this relies on raising the index of the
gradient with the Minkowski metric: the bare gradient of a scalar can have nonzero field
strength. [6] Gauge transformations compose: the trivial shift is the identity and successive shifts
add. [7] They commute with the action of the Lorentz group. [8]

### The Standard Model gauge group

The Standard Model gauge group {3} is SU(3) × SU(2) × U(1), with its projections onto the three
factors and a central discrete subgroup of sixth roots of unity. [1]

### The non-abelian theory

A general gauge theory {4} admits an arbitrary Lie group as its structure group. [TODO] Its gauge
field takes values in the Lie algebra of that group. [TODO] Matter fields carry a gauge-covariant
derivative with a definite transformation law. [TODO] The gauge field has a Yang–Mills
curvature. [TODO] That curvature transforms covariantly under gauge transformations. [TODO]
The Yang–Mills action yields the Yang–Mills field equations. [TODO] A gauge field determines
parallel transport along paths and holonomy around loops. [TODO] Gauge fields are connections on
principal bundles. [TODO] Progress on this API is tracked in a GitHub issue {5}.

## Lean References

1. Physlib/Particles/StandardModel/Basic.lean — `GaugeGroupI`, `GaugeGroupI.toSU3`,
   `GaugeGroupI.toSU2`, `GaugeGroupI.toU1`, `gaugeGroupℤ₆SubGroup`
2. Physlib/Electromagnetism/Kinematics/EMPotential.lean — `ElectromagneticPotential`
3. Physlib/Electromagnetism/Kinematics/FieldStrength.lean — `toFieldStrength`
4. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `ofGradient`,
   `gaugeTransform`, `gaugeTransform_apply`
5. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `toFieldStrength_gaugeTransform`,
   `toFieldStrength_eval_gaugeTransform`
6. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `toFieldStrength_ofGradient`,
   `toFieldStrength_eval_bareGradient_inl_inr`, `toFieldStrength_bareGradient_ne_zero`
7. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `gaugeTransform_zero`,
   `gaugeTransform_gaugeTransform`, `ofGradient_add`, `ofGradient_zero`
8. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `ofGradient_equivariant`,
   `gaugeTransform_equivariant`

## References

1. Electromagnetic Potential API map — Physlib/Electromagnetism/Kinematics/API-map.md
2. Wikipedia, Mathematical descriptions of the electromagnetic field, Gauge freedom,
   https://en.wikipedia.org/wiki/Mathematical_descriptions_of_the_electromagnetic_field#Gauge_freedom
3. Standard Model gauge group API map — Physlib/Particles/StandardModel/API-map.md
4. Wikipedia, Gauge theory, https://en.wikipedia.org/wiki/Gauge_theory
5. Physlib GitHub issue #859, https://github.com/leanprover-community/physlib/issues/859
