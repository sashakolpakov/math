import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointKernelBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionTensorModelCriterion

/-! # Field Section Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FieldSectionIsomorphism

noncomputable section

/-! Vanishing of first cohomology on every residue fiber makes the actual
section tensor comparison bijective at every field-valued point of a
Noetherian affine base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem properFlat_fieldSectionTensorComparison_bijective
    {S X P : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    (hH : ∀ x : S, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1))
    {K : Type u} [Field K] {a : P ⟶ X} {b : P ⟶ Spec (.of K)} {g : Spec (.of K) ⟶ S}
    (H : IsPullback a b f g) :
    Function.Bijective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (op ⊤)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsAffineHom g := isAffineHom_of_isAffine g
  have : IsAffineHom a := MorphismProperty.of_isPullback H.flip inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
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
  have hD : ∀ x : S, (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex (.up ℕ)).obj D).ExactAt 1 := by
    intro x
    let Hx := IsPullback.of_hasPullback f (S.fromSpecResidueField x)
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ) :=
      ht (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x))
    have : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap Hx L.sheaf U) := Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso Hx L U hUa hUe
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
        Geometric.CechTensorComparison.geometricCechTensorMap Hx L.sheaf U) := quasiIso_comp _ _
    exact FiberModelIntrinsicExactness.fiber_model_native_exact_of_H1_vanishing f L U hU hUa φ x (hH x)
  obtain ⟨hex, hmono⟩ := HilbertConstruction.Field.PointKernelBaseChange.fieldPoint_native_kernel_exact_and_mono S D hD K g
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) :=
    Framed.AffineCechTensorIsomorphism.geometricCechTensorPushforwardMap_isIso H L U hUa hUe
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) := quasiIso_comp _ _
  exact ⟨Geometric.SectionTensorInjection.geometric_sectionTensor_injective_of_model_kernel_injective H L.sheaf U hU φ
      (Tensor.KernelScalarInjection.tensor_kernel_injective_of_native_mono g.appTop.hom (D.d 0 1) hmono),
    Geometric.SectionTensorModelCriterion.geometric_sectionTensor_surjective_of_model_kernel_range H L.sheaf U hU φ
      (Tensor.KernelScalarExactness.tensor_kernel_range_of_native_exact g.appTop.hom (D.d 0 1) hex)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FieldSectionIsomorphism
