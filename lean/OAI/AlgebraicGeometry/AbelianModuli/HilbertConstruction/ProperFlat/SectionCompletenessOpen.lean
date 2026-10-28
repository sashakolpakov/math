import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModelSectionCompletenessOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiniteCechModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineCechTensorIsomorphism

/-! # Section Completeness Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionCompletenessOpen

noncomputable section

/-! Specified sections of a line bundle in a proper flat family over
a Noetherian affine base have an actual geometric completeness open.
The criterion uses the actual pulled-back sections at every field point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem properFlat_exists_sectionCompletenessOpen
    {S X : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    ∃ V : S.Opens, ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ S),
      Set.range b ⊆ (V : Set S) ↔
        Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination (pullback.snd f b).appTop.hom
          (L.pullback (pullback.fst f b)).sheaf
          (fun i => Ample.LineBundles.pullbackSection (pullback.fst f b) (s i))) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨k, W, ha, he, hw⟩ := L.exists_finite_affine_frames
  let U : ULift.{u} (Fin k) → X.Opens := fun i => W i.down
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := hw x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hUa : ∀ i, IsAffineOpen (U i) := fun i => ha i.down
  have hUe : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅
      Line.Bundles.structureModule (U i).toScheme) := fun i => he i.down
  obtain ⟨D, φ, hφ, _, hf, hp, ht⟩ := FiniteCechModel.properFlat_exists_finite_projective_cech_model f L U hU hUa
  have := hφ
  have : Module.Finite Γ(S, ⊤) (D.X 0) := hf 0
  have : Module.Projective Γ(S, ⊤) (D.X 0) := hp 0
  have : Module.Finite Γ(S, ⊤) (D.X 1) := hf 1
  have : Module.Projective Γ(S, ⊤) (D.X 1) := hp 1
  refine ⟨ModelSectionCompletenessOpen.modelSectionCompletenessOpen f L.sheaf U hU φ s, ?_⟩
  intro K _ b
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra b) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra b)
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorPushforwardMap (IsPullback.of_hasPullback f b) L.sheaf U) :=
    Framed.AffineCechTensorIsomorphism.geometricCechTensorPushforwardMap_isIso (IsPullback.of_hasPullback f b) L U hUa hUe
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra b) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap (IsPullback.of_hasPullback f b) L.sheaf U) := quasiIso_comp _ _
  exact ModelSectionCompletenessOpen.modelSectionCompletenessOpen_field_point f L.sheaf U hU φ s b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionCompletenessOpen
