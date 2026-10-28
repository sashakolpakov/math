import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeGeneratedIdeal

/-! # Graded Tail Generation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedTailGeneration.GradedHilbert

noncomputable section

/-! Finite relation modules through a bounded degree and single-degree
generation in the tail imply finite generation of the entire ideal. -/

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem homogeneousIdeal_fg_of_finite_tail_generation
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ)
    (hfg : ∀ d ≤ N, (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).FG)
    (hgen : ∀ d ≥ N, Hilbert.Polynomial.GradedHilbert.degreeRelations (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d) :
    I.toIdeal.FG := by
  let J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) := ⨆ j : Fin (N + 1), DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I j.val
  have hJI : J ≤ I := iSup_le (fun j => DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_le I j.val)
  have hIJ : I = J := by
    apply HomogeneousIdeal.ext'
    intro d f hf
    change f ∈ I.toIdeal ↔ f ∈ J.toIdeal
    constructor
    · intro hI
      by_cases hd : d ≤ N
      · have hle : DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I d ≤ J := le_iSup_of_le (⟨d, by omega⟩ : Fin (N + 1)) le_rfl
        exact hle (DegreeGeneratedIdeal.GradedHilbert.mem_degreeGeneratedIdeal I d f hf hI)
      · have hm : (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n d) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := hI
        rw [← hgen d (by omega)] at hm
        have hle : DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N ≤ J := le_iSup_of_le (⟨N, by omega⟩ : Fin (N + 1)) le_rfl
        exact hle hm
    · exact fun hfJ => hJI hfJ
  rw [hIJ]
  change (⨆ j : Fin (N + 1), DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I j.val).toIdeal.FG
  rw [HomogeneousIdeal.toIdeal_iSup]
  exact Submodule.fg_iSup _ (fun j => DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_fg I j.val (hfg j.val (by omega)))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedTailGeneration.GradedHilbert
