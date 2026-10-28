import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPELLevel

/-! # Admissible Away Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdmissibleAwayLevel.Approximation

noncomputable section

section

/-! Choose lattice coordinates from admissibility itself and construct
the actual away principal level without an extra basis input. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open _root_.Module

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include hP in
theorem admissible_lattice : Submodule.IsLattice ℚ P.lattice := by
  rcases hP with ⟨_, _, _, _, _, _, _, _, _, hL, _⟩
  exact ⟨hL.1, hL.2.1⟩

variable (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E))

def chosenCMAwayPELLevel (N : ℕ) (hN : 0 < N) : OpenSubgroup (CM.FiniteAway.Approximation.CMFiniteAway E P hP w) := by
  let := admissible_lattice E P hP
  exact CM.AwayPELLevel.Approximation.cmAwayPELLevel E P hP w (Module.Free.chooseBasis ℤ P.lattice) N hN

theorem chosenCMAwayPELLevel_mem (N : ℕ) (hN : 0 < N) (g : CM.FiniteAway.Approximation.CMFiniteAway E P hP w) :
    g ∈ chosenCMAwayPELLevel E P hP w N hN ↔ CM.AwayPELLevel.Approximation.cmAwayToPEL E P hP w g ∈ P.adelicPrincipalLevel N := Iff.rfl

end

/-! The original admissible lattice supplies its finite generation and rational spanning proofs. -/

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include hP

theorem admissible_lattice_fg : P.lattice.FG := (admissible_lattice E P hP).fg

theorem admissible_lattice_span : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤ :=
  (admissible_lattice E P hP).span_eq_top

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdmissibleAwayLevel.Approximation
