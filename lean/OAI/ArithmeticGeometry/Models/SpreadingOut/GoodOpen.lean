import OAI.ArithmeticGeometry.Models.SpreadingOut.AffineOpenGeometricDomain
import OAI.ArithmeticGeometry.Models.OpenImmersionStages

/-! # Good Open -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GoodOpen.Construction

noncomputable section

/-! A smooth geometrically irreducible scheme has a dense affine open
with a geometrically integral coefficient model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

open OAI.ArithmeticGeometry.Models.OpenImmersionStages.Constructions.Foundations

def affineLocalizationInclusion
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] (b : A) :
    Affine.Construction.affineOver K (Localization.Away b) ⟶ Affine.Construction.affineOver K A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b)))) (by
    change Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away b)))
    rw [← Spec.map_comp]
    congr 1)

instance affineLocalizationInclusion_open
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] (b : A) :
    IsOpenImmersion (affineLocalizationInclusion K A b).left :=
  IsOpenImmersion.of_isLocalization b

theorem good_open_model_from_affine_open
    (K A : Type u) [Field K] [NumberField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (X : Over (Spec (.of K))) [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (j : Affine.Construction.affineOver K A ⟶ X) [IsOpenImmersion j.left] :
    ∃ (W : Over (Spec (.of K))) (f : W ⟶ X) (M : Foundations.Constructions.CoefficientModel K W),
      IsAffine W.left ∧ IsOpenImmersion f.left ∧ IsDominant f.left ∧
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  have : IsDomain (AlgebraicClosure K ⊗[K] A) := AffineOpenGeometricDomain.Construction.affine_open_tensor_domain K (AlgebraicClosure K) A X j
  obtain ⟨b, hb, M, hconn, hirr⟩ := GeometricPrincipal.Construction.geometrically_integral_affine_has_geometric_principal_model K A
  let W := Affine.Construction.affineOver K (Localization.Away b)
  let f : W ⟶ X := affineLocalizationInclusion K A b ≫ j
  have : IsDomain (Localization.Away b) := Localization.Away.isDomain hb
  have : Nonempty W.left := inferInstanceAs (Nonempty (Spec (.of (Localization.Away b))))
  have : IsOpenImmersion f.left := inferInstanceAs
    (IsOpenImmersion ((affineLocalizationInclusion K A b).left ≫ j.left))
  have : IrreducibleSpace X.left :=
    self_of_isIntegral_of_geometrically (f := X.hom) GeometricallyIrreducible.geometrically_irreducibleSpace
  have hdom : IsDominant f.left := by
    rw [isDominant_iff, DenseRange]
    exact f.left.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  exact ⟨W, f, M, inferInstanceAs (IsAffine (Spec (.of (Localization.Away b)))),
    inferInstance, hdom, hconn, hirr⟩

theorem smooth_geometricallyIrreducible_has_good_open_model
    (K : Type u) [Field K] [NumberField K]
    (X : Over (Spec (.of K))) [Smooth X.hom] [GeometricallyIrreducible X.hom] :
    ∃ (W : Over (Spec (.of K))) (f : W ⟶ X) (M : Foundations.Constructions.CoefficientModel K W),
      IsAffine W.left ∧ IsOpenImmersion f.left ∧ IsDominant f.left ∧
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  classical
  have : IrreducibleSpace X.left := self_of_isIntegral_of_geometrically
    (f := X.hom) GeometricallyIrreducible.geometrically_irreducibleSpace
  have : IsReduced X.left := SmoothComponents.Construction.smooth_scheme_reduced X.hom
  have : IsIntegral X.left := isIntegral_of_irreducibleSpace_of_isReduced _
  let x : X.left := Classical.choice inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : X.left.Opens := U
  let Y := OpenOver.Construction.overOpen X V
  have : IsAffine Y.left := hU
  have : Nonempty V.toScheme := ⟨⟨x, hxU⟩⟩
  have hVI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral Y.left := hVI
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.left.isoSpec.inv ≫ Y.hom)
  let A := Γ(Y.left, ⊤)
  let : Algebra K A := φ.hom.toAlgebra
  let e : Y ≅ Affine.Construction.affineOver K A := Over.isoMk Y.left.isoSpec (by
    change Y.left.isoSpec.hom ≫ Spec.map φ = Y.hom
    rw [hφ, Iso.hom_inv_id_assoc])
  let j : Affine.Construction.affineOver K A ⟶ X := e.inv ≫ OpenOver.Construction.overOpenInclusion X V
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : IsOpenImmersion j.left := inferInstanceAs
    (IsOpenImmersion (e.inv.left ≫ (OpenOver.Construction.overOpenInclusion X V).left))
  have hs : Smooth (Affine.Construction.affineOver K A).hom := by
    rw [← j.w]
    infer_instance
  have hfp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
    inferInstanceAs (LocallyOfFinitePresentation (Affine.Construction.affineOver K A).hom)
  have : Algebra.FinitePresentation K A := (LocallyOfFinitePresentation.SpecMap_iff _).mp hfp
  have : Algebra.FiniteType K A := inferInstance
  exact good_open_model_from_affine_open K A X j

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GoodOpen.Construction
