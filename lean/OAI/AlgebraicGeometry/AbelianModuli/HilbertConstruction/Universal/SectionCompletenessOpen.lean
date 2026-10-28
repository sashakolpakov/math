import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenAffineBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionCompletenessOpen

/-! # Section Completeness Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessOpen

noncomputable section

/-! Universal completeness of the actual pulled-back section family is
represented by an actual open over a Noetherian affine base. Every test
scheme and every affine map to it occur in the point criterion. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def UniversallyCompleteSectionFamily {S X T : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ M)) (b : T ⟶ S) : Prop :=
  ∀ (Y : Scheme.{u}) [IsAffine Y] (a : Y ⟶ T),
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination (pullback.snd f (a ≫ b)).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst f (a ≫ b))).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst f (a ≫ b)) (s i)))

theorem properFlat_exists_universalSectionCompletenessOpen_with_fields
    {S X : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    ∃ V : S.Opens,
      (∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ S),
        Set.range b ⊆ (V : Set S) ↔
          Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination (pullback.snd f b).appTop.hom
            (L.pullback (pullback.fst f b)).sheaf
            (fun i => Ample.LineBundles.pullbackSection (pullback.fst f b) (s i)))) ∧
      (∀ (T : Scheme.{u}) (b : T ⟶ S),
        Set.range b ⊆ (V : Set S) ↔ UniversallyCompleteSectionFamily f L.sheaf s b) := by
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
  obtain ⟨D, φ, hφ, _, hf, hp, ht⟩ := ProperFlat.FiniteCechModel.properFlat_exists_finite_projective_cech_model f L U hU hUa
  have := hφ
  have : Module.Finite Γ(S, ⊤) (D.X 0) := hf 0
  have : Module.Projective Γ(S, ⊤) (D.X 0) := hp 0
  have : Module.Finite Γ(S, ⊤) (D.X 1) := hf 1
  have : Module.Projective Γ(S, ⊤) (D.X 1) := hp 1
  let V := ModelSectionCompletenessOpen.modelSectionCompletenessOpen f L.sheaf U hU φ s
  have hcomp (Y : Scheme.{u}) [IsAffine Y] (b : Y ⟶ S) :
      QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra b) φ ≫
        Geometric.CechTensorComparison.geometricCechTensorPushforwardMap (IsPullback.of_hasPullback f b) L.sheaf U) := by
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra b) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra b)
    have : IsIso (Geometric.CechTensorComparison.geometricCechTensorPushforwardMap (IsPullback.of_hasPullback f b) L.sheaf U) :=
      Framed.AffineCechTensorIsomorphism.geometricCechTensorPushforwardMap_isIso (IsPullback.of_hasPullback f b) L U hUa hUe
    exact quasiIso_comp _ _
  refine ⟨V, ?_, ?_⟩
  · intro K _ b
    have := hcomp (Spec (.of K)) b
    exact ModelSectionCompletenessOpen.modelSectionCompletenessOpen_field_point f L.sheaf U hU φ s b
  intro T b
  constructor
  · intro hb Y _ a
    have := hcomp Y (a ≫ b)
    apply OpenAffineBaseChange.modelSectionCompletenessOpen_affine_baseChange f L.sheaf U hU φ s (a ≫ b)
    rintro _ ⟨y, rfl⟩
    exact hb ⟨a y, rfl⟩
  · intro hb
    rintro _ ⟨t, rfl⟩
    let q := T.fromSpecResidueField t
    let z : Spec (T.residueField t) := (⊥ : PrimeSpectrum (T.residueField t))
    have := hcomp (Spec (T.residueField t)) (q ≫ b)
    have hq := (ModelSectionCompletenessOpen.modelSectionCompletenessOpen_field_point f L.sheaf U hU φ s (q ≫ b)).mpr
      (hb (Spec (T.residueField t)) q)
    have hz := hq ⟨z, rfl⟩
    change b (T.fromSpecResidueField t z) ∈ V at hz
    change b t ∈ V
    simpa only [Scheme.fromSpecResidueField_apply] using hz

theorem properFlat_exists_universalSectionCompletenessOpen
    {S X : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    ∃ V : S.Opens, ∀ (T : Scheme.{u}) (b : T ⟶ S),
      Set.range b ⊆ (V : Set S) ↔ UniversallyCompleteSectionFamily f L.sheaf s b := by
  obtain ⟨V, _, hV⟩ := properFlat_exists_universalSectionCompletenessOpen_with_fields f L s
  exact ⟨V, hV⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessOpen
