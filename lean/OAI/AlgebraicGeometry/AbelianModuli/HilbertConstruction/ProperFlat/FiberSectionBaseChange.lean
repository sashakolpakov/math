import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionTensorModelCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberModelKernelRange

/-! # Fiber Section Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionBaseChange

noncomputable section

/-! Vanishing of genuine first fiber cohomology makes the canonical section tensor map surjective for a proper flat line bundle over a Noetherian affine base. All covers and finite projective models are constructed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem properFlat_fiberSectionTensorComparison_surjective
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) (x : S)
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1)) :
    Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison
      (IsPullback.of_hasPullback f (S.fromSpecResidueField x)) L.sheaf).app (op ⊤)) := by
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
  have hten : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ) :=
    ht (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x))
  have hpush : IsIso (Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) :=
    Framed.AffineCechTensorIsomorphism.geometricCechTensorPushforwardMap_isIso H L U hUa hUe
  have hgeom : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso H L U hUa hUe
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) := quasiIso_comp _ _
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := quasiIso_comp _ _
  exact Geometric.SectionTensorModelCriterion.geometric_sectionTensor_surjective_of_model_kernel_range H L.sheaf U hU φ
    (FiberModelKernelRange.fiber_model_kernel_range_of_H1_vanishing f L U hU hUa φ x hH)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionBaseChange
