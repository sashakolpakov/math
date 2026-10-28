import OAI.ArithmeticGeometry.Descent.CMVariety.GeometricPrincipalCoefficients
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenImmersionStages
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality

/-! # Good Open Coefficient Models -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.GoodOpenCoefficientModels.Abelian

noncomputable section

/-! A smooth geometrically irreducible scheme has a dense affine open
with a geometrically integral coefficient model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenImmersionStages.Coefficients

def affineLocalizationInclusion
    (K A : Type) [Field K] [CommRing A] [Algebra K A] (b : A) :
    Models.SpreadingOut.Affine.Construction.affineOver K (Localization.Away b) ⟶ Models.SpreadingOut.Affine.Construction.affineOver K A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b)))) (by
    change Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away b)))
    rw [← Spec.map_comp]
    congr 1)

instance affineLocalizationInclusion_open
    (K A : Type) [Field K] [CommRing A] [Algebra K A] (b : A) :
    IsOpenImmersion (affineLocalizationInclusion K A b).left :=
  IsOpenImmersion.of_isLocalization b

theorem good_open_model_from_affine_open
    (R K A : Type) [CommRing R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (X : Over (Spec (.of K))) [Smooth X.hom] [IsIntegral X.left]
    (j : Models.SpreadingOut.Affine.Construction.affineOver K A ⟶ X) [IsOpenImmersion j.left] :
    ∃ (W : Over (Spec (.of K))) (f : W ⟶ X) (M : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K W),
      IsAffine W.left ∧ IsOpenImmersion f.left ∧ IsDominant f.left ∧
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  obtain ⟨b, hb, M, hconn, hirr⟩ := GeometricPrincipalCoefficients.Abelian.geometrically_integral_affine_has_geometric_principal_model R K A
  let W := Models.SpreadingOut.Affine.Construction.affineOver K (Localization.Away b)
  let f : W ⟶ X := affineLocalizationInclusion K A b ≫ j
  have : IsDomain (Localization.Away b) := Localization.Away.isDomain hb
  have : Nonempty W.left := inferInstanceAs (Nonempty (Spec (.of (Localization.Away b))))
  have : IsOpenImmersion f.left := inferInstanceAs
    (IsOpenImmersion ((affineLocalizationInclusion K A b).left ≫ j.left))
  have hdom : IsDominant f.left := by
    rw [isDominant_iff, DenseRange]
    exact f.left.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  exact ⟨W, f, M, inferInstanceAs (IsAffine (Spec (.of (Localization.Away b)))),
    inferInstance, hdom, hconn, hirr⟩

theorem smooth_integral_has_good_open_coefficient_model
    (R K : Type) [CommRing R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
    (X : Over (Spec (.of K))) [Smooth X.hom] [IsIntegral X.left] :
    ∃ (W : Over (Spec (.of K))) (f : W ⟶ X) (M : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K W),
      IsAffine W.left ∧ IsOpenImmersion f.left ∧ IsDominant f.left ∧
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  classical
  let x : X.left := Classical.choice inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : X.left.Opens := U
  let Y := Models.SpreadingOut.OpenOver.Construction.overOpen X V
  have : IsAffine Y.left := hU
  have : Nonempty V.toScheme := ⟨⟨x, hxU⟩⟩
  have hVI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral Y.left := hVI
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.left.isoSpec.inv ≫ Y.hom)
  let A := Γ(Y.left, ⊤)
  let : Algebra K A := φ.hom.toAlgebra
  let e : Y ≅ Models.SpreadingOut.Affine.Construction.affineOver K A := Over.isoMk Y.left.isoSpec (by
    change Y.left.isoSpec.hom ≫ Spec.map φ = Y.hom
    rw [hφ, Iso.hom_inv_id_assoc])
  let j : Models.SpreadingOut.Affine.Construction.affineOver K A ⟶ X := e.inv ≫ Models.SpreadingOut.OpenOver.Construction.overOpenInclusion X V
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : IsOpenImmersion j.left := inferInstanceAs
    (IsOpenImmersion (e.inv.left ≫ (Models.SpreadingOut.OpenOver.Construction.overOpenInclusion X V).left))
  have hs : Smooth (Models.SpreadingOut.Affine.Construction.affineOver K A).hom := by
    rw [← j.w]
    infer_instance
  have hfp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
    inferInstanceAs (LocallyOfFinitePresentation (Models.SpreadingOut.Affine.Construction.affineOver K A).hom)
  have : Algebra.FinitePresentation K A := (LocallyOfFinitePresentation.SpecMap_iff _).mp hfp
  have : Algebra.FiniteType K A := inferInstance
  exact good_open_model_from_affine_open R K A X j

end

end OAI.ArithmeticGeometry.Descent.CMVariety.GoodOpenCoefficientModels.Abelian
