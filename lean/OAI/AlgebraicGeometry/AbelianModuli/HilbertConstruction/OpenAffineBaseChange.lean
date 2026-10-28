import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModelSectionCompletenessOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.KernelOpenAffineCompleteness

/-! # Open Affine Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenAffineBaseChange

noncomputable section

/-! Every affine test mapping into the model's completeness open has
a complete family of actual pulled-back sections. The affine test is
arbitrary and need not be Noetherian, flat, or reduced over the base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem modelSectionCompletenessOpen_affine_baseChange
    {S X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U) [QuasiIsoAt φ 0]
    [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
    [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
    {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ M)) (b : Y ⟶ S)
    [hψ : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra b) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap (IsPullback.of_hasPullback f b) M U) 0]
    (hb : Set.range b ⊆ (ModelSectionCompletenessOpen.modelSectionCompletenessOpen f M U hU φ s : Set S)) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination (pullback.snd f b).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst f b)).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst f b) (s i))) := by
  let := b.appTop.hom.toAlgebra
  let t := Cech.ModelSpecifiedSectionCycles.modelSectionCycleMap f.appTop.hom M U hU φ s
  let d := (D.d 0 1).hom
  have ht := Cech.ModelSpecifiedSectionCycles.modelSectionCycleMap_cycle f.appTop.hom M U hU φ s
  have hk := Section.KernelOpenAffineCompleteness.sectionKernelOpen_affine_comparison_bijective t d ht b hb
  have htensor := (Tensor.KernelFieldCriterion.scalarExtendedCycleComparison_bijective_iff_tensor t d ht Γ(Y, ⊤)).mp hk
  have : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra b) φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (pullback.fst f b) f.appTop.hom M
        (pullback.snd f b).appTop.hom
        (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility (IsPullback.of_hasPullback f b)) U) 0 := hψ
  exact (PulledSectionCompletenessCriterion.modelSectionCycles_complete_after_pullback_iff
    (B := Affine.TensorSectionComparison.morphismGlobalAlgebra b) (pullback.fst f b) f.appTop.hom M
    (pullback.snd f b).appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility (IsPullback.of_hasPullback f b))
    s U hU φ).mp htensor

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenAffineBaseChange
