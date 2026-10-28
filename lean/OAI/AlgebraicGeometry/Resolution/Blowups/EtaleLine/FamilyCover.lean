import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.BlowupCover

/-! # Family Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FamilyCover.Construction

noncomputable section

/-! Finite actual lifted blowup covers from a coefficient generating family. -/

open _root_.AlgebraicGeometry

universe u

variable {H R ι : Type u} [CommRing H] [CommRing R] [Algebra (Polynomial H) R]

abbrev etaleLineFamilyChartGenerator (g : ι → H) :
    Option ι → Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (Ideal.span (Set.range g))
  | none => Etale.RelativeLineBlowup.Construction.etaleLineNormalElement _
  | some i => Etale.RelativeLineBlowup.Construction.etaleLineDenominator _ ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩

theorem etaleLineFamilyChartGenerator_span (g : ι → H) :
    Ideal.span (Set.range (fun i => (etaleLineFamilyChartGenerator (R := R) g i).val)) =
      Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (Ideal.span (Set.range g)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (etaleLineFamilyChartGenerator g i).property
  · apply (RetractionStep.Construction.etaleLineCenter_eq (R := R) (Ideal.span (Set.range g))).le.trans
    apply sup_le
    · rw [Ideal.map_span, ← Set.range_comp]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨some i, rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      exact Ideal.subset_span ⟨none, rfl⟩

/-- For a finite coefficient family this is a finite native affine cover
of the entire actual lifted blowup, including the normal-denominator chart. -/
def etaleLineFamilyBlowupAffineCover (g : ι → H) :
    (ReesGrading.Construction.affineBlowup (Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (Ideal.span (Set.range g)))).AffineOpenCover :=
  GeneratedBlowupCover.Construction.affineBlowupGeneratorAffineCover _ (etaleLineFamilyChartGenerator g)
    (etaleLineFamilyChartGenerator_span g)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FamilyCover.Construction
