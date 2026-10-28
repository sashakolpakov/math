import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.SheafPullback
import OAI.AlgebraicGeometry.Comparison.Betti.ConstantPullbackNormalization

/-! # Augmentation Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.AugmentationNaturality.Smooth

noncomputable section

/-! Analytic smooth pullback preserves actual locally constant zero-forms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : TopCat.{0}} [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : M ⟶ N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

theorem analyticOpenPullback_locallyConstant (U : Opens N) (a : LocallyConstant U ℂ) :
    (OpenPullback.Smooth.analyticOpenPullback f hf U).f 0 (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm F U a) =
      Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E ((Opens.map f).obj U)
        (LocallyConstant.comapₗ ℂ (SingularPresheafPullback.openPreimageMap f U).hom a) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E ((Opens.map f).obj U) 0).symm
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (SingularPresheafPullback.openPreimageMap f U) (OpenPullback.Smooth.openPreimageMap_smooth f hf U)
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv F U 0 (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm F U a)))) x v = _
  rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_symm_apply, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_apply, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_apply]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply]
  rfl

theorem analyticFormDirectImage_locallyConstant :
    Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf F N ≫ SheafPullback.Smooth.analyticFormDirectImage f hf 0 =
      ConstantPullbackNormalization.locallyConstantDirectImage f ≫
        (TopologicalSheafPullback.sheafDirectImage f).map (Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact analyticOpenPullback_locallyConstant f hf U.unop a

theorem analyticDeRhamPullback_homEquiv (n : ℕ) :
    (TopologicalSheafPullback.sheafImageAdjunction f).homEquiv _ _ ((SheafPullback.Smooth.analyticDeRhamPullback f hf).f n) =
      SheafPullback.Smooth.analyticFormDirectImage f hf n := by
  have h := SheafPullback.Smooth.analyticDeRhamPullback_normalization f hf
  erw [Adjunction.homEquiv_unit] at h ⊢
  exact congrArg (fun k => k.f n) h

theorem analyticDeRhamPullback_locallyConstant :
    (TopologicalSheafPullback.sheafInverseImage f).map (Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf F N) ≫
        (SheafPullback.Smooth.analyticDeRhamPullback f hf).f 0 =
      (TopologicalSheafPullback.locallyConstantPullbackIso f).hom ≫ Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M := by
  apply ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_left, analyticDeRhamPullback_homEquiv f hf 0,
    (TopologicalSheafPullback.sheafImageAdjunction f).homEquiv_naturality_right
      (TopologicalSheafPullback.locallyConstantPullbackIso f).hom (Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M),
    ConstantPullbackNormalization.locallyConstantPullbackIso_homEquiv]
  exact analyticFormDirectImage_locallyConstant f hf

theorem analyticDeRhamPullback_constant :
    (TopologicalSheafPullback.sheafInverseImage f).map (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham F N) ≫
        (SheafPullback.Smooth.analyticDeRhamPullback f hf).f 0 =
      (TopologicalSheafPullback.constantPullbackIso f).hom ≫ Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham E M := by
  let G := TopologicalSheafPullback.sheafInverseImage f
  let eN : ConstantSheafSections.standardConstantSheaf N ≅
      (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf N : ConstantSheafSections.ComplexSheaves N) := Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn N
  let eM : ConstantSheafSections.standardConstantSheaf M ≅
      (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) := Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M
  have he : G.map eN.hom ≫ (TopologicalSheafPullback.locallyConstantPullbackIso f).hom =
      (TopologicalSheafPullback.constantPullbackIso f).hom ≫ eM.hom := by
    change G.map eN.hom ≫ (G.map eN.inv ≫ (TopologicalSheafPullback.constantPullbackIso f).hom ≫ eM.hom) = _
    erw [← Category.assoc, ← G.map_comp, eN.hom_inv_id, G.map_id, Category.id_comp]
  change G.map (eN.hom ≫ Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf F N) ≫
    (SheafPullback.Smooth.analyticDeRhamPullback f hf).f 0 =
      (TopologicalSheafPullback.constantPullbackIso f).hom ≫ (eM.hom ≫ Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M)
  erw [G.map_comp eN.hom (Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf F N), Category.assoc,
    analyticDeRhamPullback_locallyConstant f hf, ← Category.assoc, he]
  exact Category.assoc _ _ _

def analyticPulledConstantAugmentation :
    (CochainComplex.single₀ (ConstantSheafSections.ComplexSheaves M)).obj (ConstantSheafSections.standardConstantSheaf M) ⟶
      ((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex F N) :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(TopologicalSheafPullback.constantPullbackIso f).inv ≫
      (TopologicalSheafPullback.sheafInverseImage f).map (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham F N), by
        change ((TopologicalSheafPullback.constantPullbackIso f).inv ≫
          (TopologicalSheafPullback.sheafInverseImage f).map (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham F N)) ≫
            (TopologicalSheafPullback.sheafInverseImage f).map ((Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex F N).d 0 1) = 0
        erw [Category.assoc, ← Functor.map_comp, Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham_comp_d,
          Functor.map_zero, comp_zero]⟩

theorem analyticDeRhamPullback_augmentation :
    analyticPulledConstantAugmentation (F := F) f ≫ SheafPullback.Smooth.analyticDeRhamPullback f hf =
      Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation E M := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change ((TopologicalSheafPullback.constantPullbackIso f).inv ≫
      (TopologicalSheafPullback.sheafInverseImage f).map (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham F N)) ≫
        (SheafPullback.Smooth.analyticDeRhamPullback f hf).f 0 = Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham E M
    erw [Category.assoc, analyticDeRhamPullback_constant f hf]
    exact (TopologicalSheafPullback.constantPullbackIso f).inv_hom_id_assoc _
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
      (ConstantSheafSections.standardConstantSheaf M) (n + 1) (by omega)).eq_of_src _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.AugmentationNaturality.Smooth
