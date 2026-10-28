import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FamilyCover
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.HorizontalDerivation

/-! # Generated Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.GeneratedFrame.Construction

noncomputable section

/-! Explicit dual frames and finite generating covers for actual lifted coefficient centers. -/

open _root_.Polynomial

universe u

section Generators

variable {H R ι : Type u} [CommRing H] [CommRing R] [Algebra H[X] R]

abbrev etaleLineGeneratedChartFamily (K : Ideal H) (g : ι → K) :
    Option ι → Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
  | none => Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K
  | some i => Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator K (g i)

theorem etaleLineGeneratedChartFamily_span (K : Ideal H) (g : ι → K)
    (hgen : Ideal.span (Set.range (fun i => (g i).val)) = K) :
    Ideal.span (Set.range (fun i => (etaleLineGeneratedChartFamily (R := R) K g i).val)) =
      Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (etaleLineGeneratedChartFamily K g i).property
  · apply (RetractionStep.Construction.etaleLineCenter_eq (R := R) K).le.trans
    apply sup_le
    · conv_lhs => rw [← hgen, Ideal.map_span, ← Set.range_comp]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨some i, rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      exact Ideal.subset_span ⟨none, rfl⟩

end Generators

variable (k : Type u) {H R ι : Type u} [CommRing k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]

attribute [local instance] HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

def etaleLineGeneratedFrameDerivation (δ : ι → Derivation k H H) :
    Option ι → Derivation k R R
  | none => Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)
  | some i => HorizontalDerivation.Construction.etaleLineHorizontalDerivation k (R := R) (δ i)

/-- The actual finite lifted generator family has an explicit dual frame:
the new normal derivative together with the lifted coefficient derivations. -/
theorem etaleLineGeneratedChartFamily_dual [DecidableEq ι]
    (K : Ideal H) (g : ι → K) (δ : ι → Derivation k H H)
    (hδ : ∀ i j, δ i (g j).val = if i = j then 1 else 0) :
    ∀ i j, etaleLineGeneratedFrameDerivation k (R := R) δ i
      (etaleLineGeneratedChartFamily (R := R) K g j).val = if i = j then 1 else 0 := by
  intro i j
  cases i with
  | none =>
      cases j with
      | none => exact Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate (H := H) (V := R)
      | some j =>
          change Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)
            (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (g j).val) = 0
          rw [NormalDerivation.Construction.etaleLineCoefficientMap_eq]
          exact (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).map_algebraMap (g j).val
  | some i =>
      cases j with
      | none => exact HorizontalDerivation.Construction.etaleLineHorizontalDerivation_coordinate k (δ i)
      | some j =>
          change HorizontalDerivation.Construction.etaleLineHorizontalDerivation k (δ i) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (g j).val) = _
          rw [NormalDerivation.Construction.etaleLineCoefficientMap_eq, HorizontalDerivation.Construction.etaleLineHorizontalDerivation_coefficient, hδ]
          by_cases hij : i = j <;> simp [hij]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.GeneratedFrame.Construction
