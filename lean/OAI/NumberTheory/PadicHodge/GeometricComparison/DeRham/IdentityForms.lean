import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePullback

/-! # Identity Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IdentityForms.DeRhamIdentityForms

noncomputable section

/-! The actual geometric identity pullback is the identity on
ordinary de Rham forms and on the original first three terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite ZeroObject

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

theorem sections (U : X.left.Opens) : Int.sectionPullback (𝟙 X) U = AlgHom.id R Γ(X.left, U) := by
  apply AlgHom.ext
  intro x
  rfl

theorem component (q : ℕ) (U : X.left.Opensᵒᵖ) :
    (((Int.presheafPullback (𝟙 X)).f q).app U) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (Int.sectionPullback (𝟙 X) U.unop)) q x = x
  have h : CommAlgCat.ofHom (Int.sectionPullback (𝟙 X) U.unop) =
      𝟙 (CommAlgCat.of R Γ(X.left, U.unop)) := CommAlgCat.hom_ext (sections R X U.unop)
  rw [h]
  exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_id _ q x

theorem firstThree_component (q : ℕ) (U : X.left.Opensᵒᵖ) :
    (((IntegralFirst.ThreePullback.IntegralFirstThreePullback.presheafMap (𝟙 X)).f q).app U) = 𝟙 _ := by
  change ((FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct (Int.directImagePresheaf (𝟙 X))
    (Int.presheafPullback (𝟙 X))).f q).app U = 𝟙 _
  rcases q with _ | (_ | (_ | q))
  · rw [FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_zero]
    exact component R X 0 U
  · rw [FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_one]
    exact component R X 1 U
  · rw [FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_two]
    exact component R X 2 U
  · exact (((evaluation X.left.Opensᵒᵖ (ModuleCat.{0} R)).obj U).map_isZero
      (isZero_zero (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} R))).eq_of_src _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IdentityForms.DeRhamIdentityForms
