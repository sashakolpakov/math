import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiniteProjective
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PairLinearConstraints

/-! # Partial Linear -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PartialLinear

noncomputable section

/-! Partial systems of homogeneous linear coordinates define actual
projective morphisms on their natural open domain. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
  (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)

def domain : X.carrier.Opens :=
  X.embedding ⁻¹ᵁ Projective.BasicOpen.RationalProjection.domain (Projection.FiniteProjective.FromForms.coordinates X k L)

theorem mem_domain (x : X.carrier) :
    x ∈ domain X k L ↔ ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal := by
  change X.embedding x ∈ Projective.BasicOpen.RationalProjection.domain
    (Projection.FiniteProjective.FromForms.coordinates X k L) ↔ _
  simp only [Projective.BasicOpen.RationalProjection.domain, Opens.mem_iSup,
    Projective.BasicOpen.RationalProjection.coordinateOpen, Proj.mem_basicOpen,
    Projection.FiniteProjective.FromForms.coordinate]

theorem in_domain (x : domain X k L) :
    ((domain X k L).ι ≫ X.embedding) x ∈ Projective.BasicOpen.RationalProjection.domain
      (Projection.FiniteProjective.FromForms.coordinates X k L) := x.property

def map : ((domain X k L) : Scheme) ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace k :=
  Projective.ProjectionRestriction.projection (Projection.FiniteProjective.FromForms.coordinates X k L)
    ((domain X k L).ι ≫ X.embedding) (in_domain X k L)

theorem over_base : map X k L ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k = (domain X k L).ι ≫ X.structureMap := by
  rw [map, Projective.ProjectionRestriction.over_base _ _ _
    (Projection.FiniteProjective.FromForms.constants X k L), Category.assoc, X.embedding_over]

theorem homogeneous_mem (x : domain X k L) (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading k 1) :
    a.val ∈ (map X k L x).asHomogeneousIdeal ↔
      Projection.FiniteProjective.FromForms.coordinates X k L a.val ∈ (X.embedding x.val).asHomogeneousIdeal := by
  have he := Projective.ProjectionRestriction.preimage_basicOpen
    (Projection.FiniteProjective.FromForms.coordinates X k L) ((domain X k L).ι ≫ X.embedding)
    (in_domain X k L) a.val a.property Nat.zero_lt_one
  have he' := (congrArg (fun U : ((domain X k L) : Scheme).Opens => x ∈ U) he).to_iff
  exact not_iff_not.mp he'

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PartialLinear
