import OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentProjectiveSpan
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Chern

/-! # Lefschetz -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Lefschetz.Normalization.Geometry

/-! The actual ChernClass theorem supplies the full degree-two Lefschetz input
used by DegreeTwo. This bridge can be source-checked independently of the
weight-one and geometric-product composition. -/

theorem lefschetzInput_proved : DegreeTwo.Chern.Constructions.ChernClassInput :=
  DivisorClass.Chern.ComponentProjectiveSpan.originalPresentation_lefschetz_one_one

end OAI.AlgebraicGeometry.HodgeConjecture.Lefschetz.Normalization.Geometry
