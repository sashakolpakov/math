import OAI.AlgebraicGeometry.Resolution.Blowups.GeneratedBlowupCover
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RetractionStep

/-! # Blowup Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.BlowupCover.Construction

noncomputable section

/-! Coefficient-denominator charts and the normal-denominator chart cover the actual ambient blowup. -/

open _root_.AlgebraicGeometry

universe u

variable {H R : Type u} [CommRing H] [CommRing R] [Algebra (Polynomial H) R]

def etaleLineChartGenerator (K : Ideal H) : Option K → Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
  | none => Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K
  | some a => Etale.RelativeLineBlowup.Construction.etaleLineDenominator K a

theorem etaleLineChartGenerator_span (K : Ideal H) :
    Ideal.span (Set.range (fun i => (etaleLineChartGenerator (R := R) K i).val)) = Etale.RelativeLineBlowup.Construction.etaleLineCenter K := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (etaleLineChartGenerator K i).property
  · apply (RetractionStep.Construction.etaleLineCenter_eq K).le.trans
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact Ideal.subset_span ⟨some ⟨a, ha⟩, rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      exact Ideal.subset_span ⟨none, rfl⟩

/-- These are all the chart types used by the coefficient induction, and
together they cover the whole actual blowup. -/
theorem etaleLineBlowup_chart_cover (K : Ideal H) :
    (⨆ a : K, Proj.basicOpen (ReesGrading.Construction.reesGrade (Etale.RelativeLineBlowup.Construction.etaleLineCenter K))
      (Blowup.Charts.Construction.reesGenerator (Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a))) ⊔
      Proj.basicOpen (ReesGrading.Construction.reesGrade (Etale.RelativeLineBlowup.Construction.etaleLineCenter K))
        (Blowup.Charts.Construction.reesGenerator (Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := R) K)) = ⊤ := by
  have h := GeneratedBlowupCover.Construction.affineBlowup_generator_chart_cover (Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K)
    (etaleLineChartGenerator K) (etaleLineChartGenerator_span K)
  simpa only [iSup_option, etaleLineChartGenerator, sup_comm] using h

def etaleLineBlowupAffineCover (K : Ideal H) : (ReesGrading.Construction.affineBlowup (Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K)).AffineOpenCover :=
  GeneratedBlowupCover.Construction.affineBlowupGeneratorAffineCover (Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (etaleLineChartGenerator K) (etaleLineChartGenerator_span K)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.BlowupCover.Construction
