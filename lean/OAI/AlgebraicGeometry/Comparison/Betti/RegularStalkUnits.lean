import OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation
import OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation

/-! # Regular Stalk Units -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RegularStalkUnits

noncomputable section

/-! The original open-section evaluation is the complex point's
structure-sheaf evaluation. A nonzero value gives a unit in the
actual algebraic local ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation

theorem sectionEvaluationOn_complexSectionValue (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens)
    (s : Γ(X.left, U)) (p : Open.AffineIsoEvaluation.analyticOpen X U) :
    Open.AffineIsoEvaluation.sectionEvaluationOn X U s p = RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p.val.left U p.property s := by
  let q := (Open.AffineIsoEvaluation.openPointHomeomorph X U).symm p
  have hq : q.left ≫ U.ι = p.val.left :=
    congrArg (fun r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => r.left)
      (congrArg Subtype.val ((Open.AffineIsoEvaluation.openPointHomeomorph X U).apply_symm_apply p))
  have ht : RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue q.left ⊤ (by trivial) (U.topIso.inv s) =
      RegularFunctions.globalEvaluation q (U.topIso.inv s) := by
    have ha : q.left.appLE ⊤ ⊤ (by simp) = q.left.appTop := q.left.appLE_eq_app
    exact congrArg (fun f : Γ(U.toScheme, ⊤) ⟶ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) =>
      (Scheme.ΓSpecIso (.of ℂ)).hom (f (U.topIso.inv s))) ha
  exact (ht.symm.trans (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_open U q.left s).symm).trans
    (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_congr _ _ hq U _ p.property s)

theorem regular_germ_isUnit_of_value {X : Scheme.{0}} (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (U : X.Opens)
    (hp : p (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U) (s : Γ(X, U))
    (hs : RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p U hp s ≠ 0) :
    IsUnit (X.presheaf.germ U (p (default : Foundations.Scheme.ProjectiveSpace.complexBase)) hp s) := by
  let hU : (⊤ : Foundations.Scheme.ProjectiveSpace.complexBase.Opens) ≤ p ⁻¹ᵁ U := by
    intro x _
    change p x ∈ U
    rwa [Subsingleton.elim x (default : Foundations.Scheme.ProjectiveSpace.complexBase)]
  have hu : IsUnit (p.appLE U ⊤ hU s) := by
    have h := (isUnit_iff_ne_zero.mpr hs).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom
    change IsUnit ((Scheme.ΓSpecIso (.of ℂ)).inv
      ((Scheme.ΓSpecIso (.of ℂ)).hom (p.appLE U ⊤ hU s))) at h
    rwa [Iso.hom_inv_id_apply] at h
  apply isUnit_of_map_unit (p.stalkMap (default : Foundations.Scheme.ProjectiveSpace.complexBase)).hom
  rw [Scheme.Hom.germ_stalkMap_apply]
  have hu' := hu.map (Foundations.Scheme.ProjectiveSpace.complexBase.presheaf.Γgerm (default : Foundations.Scheme.ProjectiveSpace.complexBase)).hom
  change IsUnit (Foundations.Scheme.ProjectiveSpace.complexBase.presheaf.germ ⊤ (default : Foundations.Scheme.ProjectiveSpace.complexBase) (by trivial)
    (Foundations.Scheme.ProjectiveSpace.complexBase.presheaf.map (homOfLE hU).op (p.app U s))) at hu'
  exact (congrArg IsUnit (Foundations.Scheme.ProjectiveSpace.complexBase.presheaf.germ_res_apply (homOfLE hU)
    (default : Foundations.Scheme.ProjectiveSpace.complexBase) (by trivial) (p.app U s))).mp hu'

end

end OAI.AlgebraicGeometry.Comparison.Betti.RegularStalkUnits
