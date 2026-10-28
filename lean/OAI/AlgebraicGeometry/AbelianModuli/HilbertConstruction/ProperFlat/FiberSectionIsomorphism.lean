import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionTensorInjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberKernelTensorInjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionBaseChange

/-! # Fiber Section Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionIsomorphism

noncomputable section

/-! Vanishing of genuine first fiber cohomology makes the canonical section tensor map bijective for a proper flat line bundle over a Noetherian affine base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem properFlat_fiberSectionTensorComparison_bijective
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) (x : S)
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1)) :
    Function.Bijective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison
      (IsPullback.of_hasPullback f (S.fromSpecResidueField x)) L.sheaf).app (op ⊤)) := by
  refine ⟨?_, FiberSectionBaseChange.properFlat_fiberSectionTensorComparison_surjective f L x hH⟩
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨k, V, ha, he, hcover⟩ := L.exists_finite_affine_frames
  let U : ULift.{u} (Fin k) → X.Opens := fun i => V i.down
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hUa : ∀ i, IsAffineOpen (U i) := fun i => ha i.down
  have hUe : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅
      Line.Bundles.structureModule (U i).toScheme) := fun i => he i.down
  obtain ⟨D, φ, hφ, _, hfin, hproj, ht⟩ := FiniteCechModel.properFlat_exists_finite_projective_cech_model f L U hU hUa
  have := hφ
  have : Module.Finite Γ(S, ⊤) (D.X 0) := hfin 0
  have : Module.Projective Γ(S, ⊤) (D.X 0) := hproj 0
  have : Module.Finite Γ(S, ⊤) (D.X 1) := hfin 1
  have : Module.Projective Γ(S, ⊤) (D.X 1) := hproj 1
  have : Module.Finite Γ(S, ⊤) (D.X 2) := hfin 2
  have : Module.Projective Γ(S, ⊤) (D.X 2) := hproj 2
  let H := IsPullback.of_hasPullback f (S.fromSpecResidueField x)
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ) :=
    ht (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x))
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) :=
    Framed.AffineCechTensorIsomorphism.geometricCechTensorPushforwardMap_isIso H L U hUa hUe
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso H L U hUa hUe
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) := quasiIso_comp _ _
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := quasiIso_comp _ _
  exact Geometric.SectionTensorInjection.geometric_sectionTensor_injective_of_model_kernel_injective H L.sheaf U hU φ
    (FiberKernelTensorInjection.fiber_model_kernel_tensor_injective_of_H1_vanishing f L U hU hUa φ x hH)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionIsomorphism
