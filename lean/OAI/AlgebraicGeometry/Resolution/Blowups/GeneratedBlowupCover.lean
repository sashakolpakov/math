import OAI.AlgebraicGeometry.Resolution.Blowups.ReesPresentation
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Cover

/-! # Generated Blowup Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GeneratedBlowupCover.Construction

noncomputable section

/-! Actual affine blowup covers from any specified generating family of the center ideal. -/

open _root_.AlgebraicGeometry

universe u

variable {R ι : Type u} [CommRing R] (I : Ideal R) (a : ι → I)

theorem reesFamily_adjoin_zero (hgen : Submodule.span R (Set.range a) = ⊤) :
    Algebra.adjoin (ReesGrading.Construction.reesGrade I 0) (Set.range (fun i => Blowup.Charts.Construction.reesGenerator I (a i))) = ⊤ := by
  have hle : Algebra.adjoin R (Set.range (fun i => Blowup.Charts.Construction.reesGenerator I (a i))) ≤
      (Algebra.adjoin (ReesGrading.Construction.reesGrade I 0) (Set.range (fun i => Blowup.Charts.Construction.reesGenerator I (a i)))).restrictScalars R :=
    Algebra.adjoin_le (fun _ hx => Algebra.subset_adjoin (R := ReesGrading.Construction.reesGrade I 0) hx)
  rw [ReesPresentation.Construction.reesFamily_adjoin I a hgen] at hle
  apply top_le_iff.mp
  intro x _
  exact hle (by trivial)

/-- The selected center generators give a cover of the actual blowup,
without assuming that the center is nonzero or the base is integral. -/
theorem affineBlowup_generator_chart_cover
    (hgen : Ideal.span (Set.range (fun i => (a i).val)) = I) :
    (⨆ i : ι, Proj.basicOpen (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I (a i))) = ⊤ := by
  have hs : Submodule.span R (Set.range a) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I (fun i => (a i).property)).mpr hgen
  exact Proj.iSup_basicOpen_eq_top' (ReesGrading.Construction.reesGrade I) (fun i => Blowup.Charts.Construction.reesGenerator I (a i))
    (fun i => ⟨1, Blowup.Charts.Construction.reesGenerator_mem I (a i)⟩) (reesFamily_adjoin_zero I a hs)

/-- The preceding open-set cover as a native scheme affine open cover. -/
def affineBlowupGeneratorAffineCover
    (hgen : Ideal.span (Set.range (fun i => (a i).val)) = I) : (ReesGrading.Construction.affineBlowup I).AffineOpenCover where
  I₀ := ι
  X i := .of (Blowup.Charts.Construction.blowupChart I (a i))
  f i := Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I (a i)) (Blowup.Charts.Construction.reesGenerator_mem I (a i)) (by decide)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((affineBlowup_generator_chart_cover I a hgen).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι (ReesGrading.Construction.reesGrade I) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((affineBlowup_generator_chart_cover I a hgen).ge (Set.mem_univ x))).choose_spec

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GeneratedBlowupCover.Construction
