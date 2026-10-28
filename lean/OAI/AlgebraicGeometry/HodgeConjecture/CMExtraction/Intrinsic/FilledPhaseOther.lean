import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ResidualCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseBasis
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPhaseColumn

/-! # Filled Phase Other -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPhaseOther

noncomputable section

/-! The original filled PEL phase matrix retains each original
rational matrix entry at every prime other than q. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseBasis.TestTransport OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ResidualCoordinates.ParameterChoices

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))

omit [IsGalois ℚ E] in
theorem nativeFilledPhase_other_entry (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    (i j : (Fin s × Fin 3) ⊕ (Fin s × Fin 3)) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E D.reference e (FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ) i j) =
      algebraMap ℚ (Padic p) (RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E D.reference e γ i j) :=
  (congrArg (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p)
    (PEL.PhaseBasis.TestTransport.pelPhaseMatrix_column E e D.reference (FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ) i j)).trans
    ((ResidualCoordinates.ParameterChoices.nativeFilledPEL_other_coordinate E D hg e γ (e.symm (Pi.single j 1)) i p hpq).trans
      (congrArg (algebraMap ℚ (Padic p)) (RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix_column E D.reference e γ i j).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPhaseOther
