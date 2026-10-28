import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveSectionKernelOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelFieldCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledSectionCompletenessCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechTensorComparison

/-! # Model Section Completeness Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModelSectionCompletenessOpen

noncomputable section

/-! A finite projective Cech model defines an actual open whose
field-valued points are precisely the points where the specified pulled-back
sections form a complete basis. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U) [QuasiIsoAt φ 0]
variable [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
variable [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
variable {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ M))

def modelSectionCompletenessOpen : S.Opens :=
  HilbertConstruction.Finite.ProjectiveSectionKernelOpen.finiteProjectiveSectionKernelOpen (Cech.ModelSpecifiedSectionCycles.modelSectionCycleMap f.appTop.hom M U hU φ s) (D.d 0 1).hom

theorem modelSectionCompletenessOpen_field_point
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S)
    [hψ : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra b) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap (IsPullback.of_hasPullback f b) M U) 0] :
    Set.range b ⊆ (modelSectionCompletenessOpen f M U hU φ s : Set S) ↔
      Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination (pullback.snd f b).appTop.hom
        ((Scheme.Modules.pullback (pullback.fst f b)).obj M)
        (fun i => Ample.LineBundles.pullbackSection (pullback.fst f b) (s i))) := by
  let := b.appTop.hom.toAlgebra
  let t := Cech.ModelSpecifiedSectionCycles.modelSectionCycleMap f.appTop.hom M U hU φ s
  let d := (D.d 0 1).hom
  have ht := Cech.ModelSpecifiedSectionCycles.modelSectionCycleMap_cycle f.appTop.hom M U hU φ s
  have hr := HilbertConstruction.Finite.ProjectiveSectionKernelOpen.finiteProjectiveSectionKernelOpen_field_point t d ht b
  have he := Tensor.KernelFieldCriterion.scalarExtendedCycleComparison_bijective_iff_tensor t d ht Γ(Spec (.of K), ⊤)
  have : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra b) φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (pullback.fst f b) f.appTop.hom M
        (pullback.snd f b).appTop.hom
        (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility (IsPullback.of_hasPullback f b)) U) 0 := hψ
  have hc := PulledSectionCompletenessCriterion.modelSectionCycles_complete_after_pullback_iff
    (B := Affine.TensorSectionComparison.morphismGlobalAlgebra b) (pullback.fst f b) f.appTop.hom M
    (pullback.snd f b).appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility (IsPullback.of_hasPullback f b))
    s U hU φ
  exact hr.trans (he.trans hc)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModelSectionCompletenessOpen
