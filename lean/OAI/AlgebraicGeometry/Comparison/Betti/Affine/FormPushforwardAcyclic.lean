import OAI.AlgebraicGeometry.Comparison.Betti.PushforwardCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.AffineAcyclicity

/-! # Form Pushforward Acyclic -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.FormPushforwardAcyclic

noncomputable section

/-! Direct images of the original form sheaves from affine opens are acyclic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsSeparated X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U)

include hU in
theorem affineOpen_algebraicForms_localAcyclic (n : ℕ)
    (V : X.left.Opens) (x : V) :
    ∃ W : X.left.Opens, W ≤ V ∧ x.val ∈ W ∧ ∀ q,
      Subsingleton (Sheaf.H
        ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat
          ((Opens.map U.inclusion').obj W).isOpenEmbedding).obj
          (ExteriorAcyclicity.algebraicFormAdditiveSheaf (Open.AffineIsoEvaluation.openOver X U) n)) (q + 1)) := by
  have : IsAffine U := hU
  have : Smooth (Open.AffineIsoEvaluation.openOver X U).hom := inferInstanceAs (Smooth (U.ι ≫ X.hom))
  have : IsAffineHom U.ι := IsAffineHom.of_comp U.ι X.hom
  obtain ⟨W, hWV, hxW, hW, _⟩ := StandardSmoothBasis.exists_standardSmooth_openOver_le X V x
  refine ⟨W, hWV, hxW, fun q => ?_⟩
  exact Betti.Smooth.AffineAcyclicity.smooth_affineOpen_algebraicForms_acyclic (Open.AffineIsoEvaluation.openOver X U)
    (U.ι ⁻¹ᵁ W) ((show IsAffineOpen W from hW).preimage U.ι) n q

include hU in
theorem affineOpen_algebraicFormPushforward_acyclic (n q : ℕ) :
    Subsingleton (Sheaf.H
      ((TopCat.Sheaf.pushforward AddCommGrpCat U.inclusion').obj
        ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat U.isOpenEmbedding).obj
          (ExteriorAcyclicity.algebraicFormAdditiveSheaf X n))) (q + 1)) := by
  have : IsAffine U := hU
  have : IsAffine (Open.AffineIsoEvaluation.openOver X U).left := hU
  have : Smooth (Open.AffineIsoEvaluation.openOver X U).hom := inferInstanceAs (Smooth (U.ι ≫ X.hom))
  have : Subsingleton (Sheaf.H (ExteriorAcyclicity.algebraicFormAdditiveSheaf (Open.AffineIsoEvaluation.openOver X U) n) (q + 1)) :=
    Betti.Smooth.AffineAcyclicity.smooth_algebraicForms_acyclic (Open.AffineIsoEvaluation.openOver X U) n q
  have hp : Subsingleton (Sheaf.H
      ((TopCat.Sheaf.pushforward AddCommGrpCat U.inclusion').obj
        (ExteriorAcyclicity.algebraicFormAdditiveSheaf (Open.AffineIsoEvaluation.openOver X U) n)) (q + 1)) :=
    @PushforwardCohomology.Cech.pushforward_cohomology_subsingleton (TopCat.of U) (TopCat.of X.left) U.inclusion'
    (ExteriorAcyclicity.algebraicFormAdditiveSheaf (Open.AffineIsoEvaluation.openOver X U) n)
    (affineOpen_algebraicForms_localAcyclic X U hU n) (q + 1)
    (Betti.Smooth.AffineAcyclicity.smooth_algebraicForms_acyclic (Open.AffineIsoEvaluation.openOver X U) n q)
  let H := Sheaf.functorH (Opens.grothendieckTopology X.left) (q + 1)
  have : Subsingleton (H.obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat U.inclusion').obj
        (ExteriorAcyclicity.algebraicFormAdditiveSheaf (Open.AffineIsoEvaluation.openOver X U) n))) := hp
  let e := H.mapIso ((TopCat.Sheaf.pushforward AddCommGrpCat U.inclusion').mapIso
    (LocalFormAcyclicity.algebraicFormAdditiveOpenRestrictionIso (Open.AffineIsoEvaluation.openInclusion X U) n))
  exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.FormPushforwardAcyclic
