import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointIdeal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConePreimage

/-! # Generic -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Generic

noncomputable section

/-! The actual generic point of the projective cone maps to the
chosen generic point of its base support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

variable {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
  (hL : LinearIndependent ℂ L) (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m)

def point : Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L) := ⟨Projective.ConeSupport.genericPoint L hL η, Projective.ConeSupport.point_in_domain L hL η⟩

theorem map_point : Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L) (point L hL η) = η := by
  have he := Projection.PointIdeal.Rational.ideal (Projective.ConeSupport.coordinates L)
    (HomogeneousCoordinateMap.ofForms_C _ _) (point L hL η)
  have hc : (Projective.ConeSupport.ideal L η).comap (Projective.ConeSupport.coordinates L) = η.asHomogeneousIdeal := by
    apply HomogeneousIdeal.ext
    exact LinearPrimeIdeal.Projection.comap_map L hL η.asHomogeneousIdeal.toIdeal
  apply ProjectiveSpectrum.ext
  exact he.trans hc

theorem mem_cone_iff (x : Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)) :
    x.val ∈ Projective.ConeSupport.support L hL η ↔ Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L) x ∈
      (irreducibleSetEquivPoints.symm η : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace m)) := by
  have he := Projective.ConePreimage.mem_iff L hL η (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).ι
    (Projection.PointIdeal.Rational.in_domain (Projective.ConeSupport.coordinates L)) x
  rw [Projection.PointIdeal.Rational.restriction_eq] at he
  exact he

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Generic
