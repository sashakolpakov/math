import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.HorizontalDerivation
import OAI.AlgebraicGeometry.Resolution.Blowups.DualFrameBlowupSmooth

/-! # Frame Center Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FrameCenterSmooth.Construction

noncomputable section

/-! Smoothness of actual hypersurface-center blowups lifted from arbitrary dual coordinate families. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {H R ι : Type u} [CommRing k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
  [Algebra.Smooth k H] [Fintype ι] [DecidableEq ι]

attribute [local instance] HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

/-- Lifting a coefficient center with dual coordinate derivations adds the
normal equation and its normal derivation. Every chart of the actual lifted
blowup is smooth over the unchanged base, in any coefficient dimension. -/
theorem etaleLine_frame_center_blowup_smooth (g : ι → H) (δ : ι → Derivation k H H)
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (Ideal.span (Set.range g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let : Algebra.Smooth H H[X] := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth k H[X] := Algebra.Smooth.comp k H H[X]
  let : Algebra.Smooth k R := Algebra.Smooth.comp k H[X] R
  let K := Ideal.span (Set.range g)
  let D := Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)
  let v : Option ι → R
    | none => algebraMap H[X] R X
    | some i => algebraMap H R (g i)
  let F : Option ι → Derivation k R R
    | none => D
    | some i => HorizontalDerivation.Construction.etaleLineHorizontalDerivation k (R := R) (δ i)
  have hF : ∀ i j, F i (v j) = if i = j then 1 else 0 := by
    intro i j
    cases i with
    | none =>
        cases j with
        | none => exact Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate (H := H) (V := R)
        | some j =>
            exact (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).map_algebraMap (g j)
    | some i =>
        cases j with
        | none => exact HorizontalDerivation.Construction.etaleLineHorizontalDerivation_coordinate k (δ i)
        | some j =>
            change HorizontalDerivation.Construction.etaleLineHorizontalDerivation k (δ i) (algebraMap H R (g j)) = _
            rw [HorizontalDerivation.Construction.etaleLineHorizontalDerivation_coefficient, hδ]
            by_cases hij : i = j <;> simp [hij]
  have hcenter : Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K = Ideal.span (Set.range v) := by
    apply le_antisymm
    · rw [RetractionStep.Construction.etaleLineCenter_eq, NormalDerivation.Construction.etaleLineCoefficientMap_eq]
      apply sup_le
      · change (Ideal.span (Set.range g)).map (algebraMap H R) ≤ _
        rw [Ideal.map_span, ← Set.range_comp]
        apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact Ideal.subset_span ⟨some i, rfl⟩
      · apply Ideal.span_le.mpr
        rintro _ ⟨rfl⟩
        exact Ideal.subset_span ⟨none, rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      cases i with
      | none => exact (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := R) K).property
      | some i =>
          have hgi : Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (g i) ∈ Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K :=
            Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩))
          rw [NormalDerivation.Construction.etaleLineCoefficientMap_eq] at hgi
          exact hgi
  rw [hcenter]
  exact DualFrameBlowupSmooth.Construction.dual_derivation_family_blowup_smooth v F hF

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FrameCenterSmooth.Construction
