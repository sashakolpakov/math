import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.FiberSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Generic
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentSmooth

/-! # Stalk Ideal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.StalkIdeal

noncomputable section

/-! On the natural domain of a linear projection, the native reduced
cone stalk over the generic base point is the quotient by the extended
maximal ideal of that base stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport

variable {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
  (hL : LinearIndependent ℂ L) (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m)

def onDomain : IrreducibleCloseds (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)) :=
  irreducibleSetEquivPoints.symm (Generic.Projection.point L hL η)

theorem generic_point : CycleClass.Thom.IntersectionGeometry.supportPoint (onDomain L hL η) = Generic.Projection.point L hL η :=
  irreducibleSetEquivPoints.apply_symm_apply _

theorem generic_image : (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).ι (CycleClass.Thom.IntersectionGeometry.supportPoint (onDomain L hL η)) =
    CycleClass.Thom.IntersectionGeometry.supportPoint (Projective.ConeSupport.support L hL η) := by
  rw [generic_point]
  exact (irreducibleSetEquivPoints.apply_symm_apply _).symm

theorem mem_iff (x : Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)) :
    x ∈ (onDomain L hL η : Set (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L))) ↔ x.val ∈ Projective.ConeSupport.support L hL η := by
  change x ∈ closure ({Generic.Projection.point L hL η} : Set (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L))) ↔
    x.val ∈ closure ({Projective.ConeSupport.genericPoint L hL η} : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
  exact specializes_iff_mem_closure.symm.trans
    ((Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).ι.isOpenEmbedding.isInducing.specializes_iff.symm.trans
      specializes_iff_mem_closure)

theorem mem_of_map (x : Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)) (hx : Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L) x = η) :
    x ∈ (onDomain L hL η : Set (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L))) := by
  apply (mem_iff L hL η x).mpr
  apply (Generic.Projection.mem_cone_iff L hL η x).mpr
  rw [hx]
  exact subset_closure (Set.mem_singleton η)

def moduleEquiv (x : Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)) (hx : Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L) x = η) :
    CycleClass.Thom.IntersectionGeometry.localSupportModule (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)) (onDomain L hL η) x (mem_of_map L hL η x hx) ≃ₗ[
      (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).toScheme.presheaf.stalk x]
      (((Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).toScheme.presheaf.stalk x) ⧸
        (IsLocalRing.maximalIdeal ((Foundations.Scheme.ProjectiveSpace.projectiveSpace m).presheaf.stalk (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L) x))).map
          ((Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)).stalkMap x).hom) := by
  let : SmoothOfRelativeDimension (n - m) (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) := IndependentSmooth.Projection.smooth L hL
  let : Smooth (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) := SmoothOfRelativeDimension.smooth (n - m) _
  apply ProjectionFormula.Smooth.FiberSupport.moduleEquiv (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) x (onDomain L hL η)
    (mem_of_map L hL η x hx)
  · rw [generic_point, Generic.Projection.map_point, hx]
  · intro z hz
    exact mem_of_map L hL η z (hz.trans hx)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.StalkIdeal
