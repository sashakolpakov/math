import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecScalarSections
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ScalarMaps

/-! # Spec Stalk Algebra -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecStalkAlgebra

noncomputable section

/-! The native affine stalk map is an algebra homomorphism for the
coefficient-field action induced by the actual scheme structure map. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k R : Type) [Field k] [CommRing R] [Algebra k R]

def toStalk (x : Spec (.of R)) :
    letI := Stalk.PointAlgebra.scalarAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k R))) x
    R →ₐ[k] (Spec (.of R)).presheaf.stalk x := by
  let := Stalk.PointAlgebra.scalarAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k R))) x
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
  exact (Stalk.ScalarMaps.germ (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤ x trivial).comp
    (SpecScalarSections.equivalence k R).toAlgHom

theorem apply (x : Spec (.of R)) (r : R) : SpecStalkAlgebra.toStalk k R x r = StructureSheaf.toStalk R x r := rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecStalkAlgebra
