import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPELLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenLevelTransport

/-! # Away Level Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayLevelTransport.Approximation

noncomputable section

/-! A principal containment chosen in the original PEL group forces
the filled away level into the same prescribed source open subgroup. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open _root_.Module

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E))

theorem cmAwayToPEL_fill (g : FiniteAway.Approximation.CMFiniteAway E P hP w) :
    AwayPELLevel.Approximation.cmAwayToPEL E P hP w g =
      AwayPELLevel.Approximation.cmOriginalPELHomeomorph E P hP (RestrictedInsert.Approximation.restrictedInsertPlace _ w g) := rfl

variable {J : Type*} [Fintype J] [DecidableEq J]
  [Submodule.IsLattice ℚ P.lattice] (b : Basis J ℤ P.lattice)

theorem cmAwayPELLevel_fill_mem (N : ℕ) (hN : 0 < N)
    (K : OpenSubgroup (FiniteAway.Approximation.CMFiniteSU E P hP))
    (hK : P.adelicPrincipalLevel N ≤ (OpenLevelTransport.Approximation.transportOpenLevel (AwayPELLevel.Approximation.cmOriginalPELHomeomorph E P hP) K).toSubgroup)
    (g : FiniteAway.Approximation.CMFiniteAway E P hP w) (hg : g ∈ AwayPELLevel.Approximation.cmAwayPELLevel E P hP w b N hN) :
    RestrictedInsert.Approximation.restrictedInsertPlace _ w g ∈ K :=
  (OpenLevelTransport.Approximation.transportOpenLevel_mem (AwayPELLevel.Approximation.cmOriginalPELHomeomorph E P hP) K (RestrictedInsert.Approximation.restrictedInsertPlace _ w g)).mp
    (hK ((AwayPELLevel.Approximation.cmAwayPELLevel_mem E P hP w b N hN g).mp hg))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayLevelTransport.Approximation
