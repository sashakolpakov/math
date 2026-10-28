import OAI.AlgebraicGeometry.Comparison.Betti.ConstantPullbackNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.SingularGlobalNaturality

/-! # Singular Augmentation Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SingularAugmentationNaturality

noncomputable section

/-! The actual singular pullback preserves the point-evaluation augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {M N : TopCat.{0}} (f : M ⟶ N)

theorem singularSheafDirectImage_augmentation :
    AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation N ≫ (SingularGlobalNaturality.singularSheafDirectImage f).f 0 =
      ConstantPullbackNormalization.locallyConstantDirectImage f ≫
        (TopologicalSheafPullback.sheafDirectImage f).map (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation M) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have hN := congrArg (fun k => k.app U) (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation_hom N)
  have hM := congrArg (fun k => k.app (op ((Opens.map f).obj U.unop)))
    (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation_hom M)
  change (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation N).hom.app U ≫
    ((SingularGlobalNaturality.singularSheafDirectImage f).f 0).hom.app U =
      ModuleCat.ofHom (LocallyConstant.comapₗ ℂ (SingularPresheafPullback.openPreimageMap f U.unop).hom) ≫
        (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation M).hom.app (op ((Opens.map f).obj U.unop))
  erw [hN, hM]
  change ((AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison.locallyConstantSingularAugmentation N).app U ≫ _) ≫ _ =
    _ ≫ ((AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison.locallyConstantSingularAugmentation M).app (op ((Opens.map f).obj U.unop)) ≫ _)
  erw [Category.assoc, SingularGlobalNaturality.singularSheafDirectImage_unit f 0 U.unop, ← Category.assoc]
  have h := AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_naturality (ModuleCat.of ℂ ℂ)
    (SingularPresheafPullback.openPreimageMap f U.unop)
  exact congrArg (fun k => k ≫
    (CategoryTheory.toSheafify (Opens.grothendieckTopology M)
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) M 0)).app
        (op ((Opens.map f).obj U.unop))) h.symm

theorem singularSheafPullback_homEquiv (n : ℕ) :
    (TopologicalSheafPullback.sheafImageAdjunction f).homEquiv _ _ ((SingularGlobalNaturality.singularSheafPullback f).f n) =
      (SingularGlobalNaturality.singularSheafDirectImage f).f n := by
  have h := SingularGlobalNaturality.singularSheafPullback_normalization f
  erw [Adjunction.homEquiv_unit] at h ⊢
  exact congrArg (fun k => k.f n) h

theorem singularSheafPullback_augmentation :
    (TopologicalSheafPullback.sheafInverseImage f).map (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation N) ≫
        (SingularGlobalNaturality.singularSheafPullback f).f 0 =
      (TopologicalSheafPullback.locallyConstantPullbackIso f).hom ≫ AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation M := by
  apply ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_left, singularSheafPullback_homEquiv]
  erw [(TopologicalSheafPullback.sheafImageAdjunction f).homEquiv_naturality_right
    (TopologicalSheafPullback.locallyConstantPullbackIso f).hom (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation M)]
  erw [ConstantPullbackNormalization.locallyConstantPullbackIso_homEquiv]
  exact singularSheafDirectImage_augmentation f

theorem singularSheafPullback_resolution [StronglyLocallyContractibleSpace N] :
    ResolutionExactImage.cochainAugmentation (TopologicalSheafPullback.pulledSingularResolutionData f) ≫
      SingularGlobalNaturality.singularSheafPullback f = AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafResolutionMap M := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change ((TopologicalSheafPullback.locallyConstantPullbackIso f).inv ≫
      (TopologicalSheafPullback.sheafInverseImage f).map (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation N)) ≫
        (SingularGlobalNaturality.singularSheafPullback f).f 0 = AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation M
    erw [Category.assoc, singularSheafPullback_augmentation]
    exact (TopologicalSheafPullback.locallyConstantPullbackIso f).inv_hom_id_assoc _
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
      (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) (n + 1) (by omega)).eq_of_src _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.SingularAugmentationNaturality
