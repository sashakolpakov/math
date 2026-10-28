import OAI.AlgebraicGeometry.Resolution.Blowups.GeneratedBlowupCover

/-! # Two Generator Blowup Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TwoGeneratorBlowupCover.Construction

noncomputable section

/-! A finite affine cover for an actual blowup with two selected center generators. -/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

def pairBlowupChartGenerator (a b : I) : Option (ULift.{u} Unit) → I
  | none => b
  | some _ => a

theorem pairBlowupChartGenerator_span (a b : I)
    (hI : I = Ideal.span {a.val} ⊔ Ideal.span {b.val}) :
    Ideal.span (Set.range (fun i => (pairBlowupChartGenerator I a b i).val)) = I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (pairBlowupChartGenerator I a b i).property
  · apply hI.le.trans
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      exact Ideal.subset_span ⟨some ⟨()⟩, rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      exact Ideal.subset_span ⟨none, rfl⟩

/-- The two denominator charts cover the actual blowup scheme. -/
theorem affineBlowup_pair_chart_cover (a b : I)
    (hI : I = Ideal.span {a.val} ⊔ Ideal.span {b.val}) :
    Proj.basicOpen (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) ⊔
      Proj.basicOpen (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I b) = ⊤ := by
  have h := GeneratedBlowupCover.Construction.affineBlowup_generator_chart_cover I (pairBlowupChartGenerator I a b)
    (pairBlowupChartGenerator_span I a b hI)
  simpa only [iSup_option, pairBlowupChartGenerator, iSup_const, sup_comm] using h

def pairBlowupAffineCover (a b : I)
    (hI : I = Ideal.span {a.val} ⊔ Ideal.span {b.val}) : (ReesGrading.Construction.affineBlowup I).AffineOpenCover :=
  GeneratedBlowupCover.Construction.affineBlowupGeneratorAffineCover I (pairBlowupChartGenerator I a b)
    (pairBlowupChartGenerator_span I a b hI)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TwoGeneratorBlowupCover.Construction
