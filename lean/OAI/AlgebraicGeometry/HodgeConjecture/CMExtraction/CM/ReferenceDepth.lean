import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELLevelTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPELLevel

/-! # Reference Depth -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ReferenceDepth.Approximation

noncomputable section

/-! Source-level cofinality through the actual original PEL homeomorphism. -/

open scoped Classical _root_.NumberField

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem cm_original_principal_depth (L : OpenSubgroup (FiniteAway.Approximation.CMFiniteSU E P hP))
    (hfg : P.lattice.FG)
    (hspan : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ∣ N → ∀ g : FiniteAway.Approximation.CMFiniteSU E P hP,
      AwayPELLevel.Approximation.cmOriginalPELHomeomorph E P hP g ∈ P.adelicPrincipalLevel N → g ∈ L :=
  CMPELLevelTransport.Approximation.cm_source_level_principal_depth E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P hP.2.1 hP.2.2.1 L hfg hspan

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ReferenceDepth.Approximation
