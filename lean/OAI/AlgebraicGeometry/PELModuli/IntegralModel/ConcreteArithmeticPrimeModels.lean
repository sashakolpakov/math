import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ModelsFromGraphFactory
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GraphPowerLocusFactory

/-! # Concrete Arithmetic Prime Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConcreteArithmeticPrimeModels

noncomputable section

/-! The actual arithmetic prime-level PEL models for an admissible datum.
All graph-parameter, pure-moduli, and equation inputs are proved. -/

theorem actualArithmeticPrimePELModels
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (hs : 0 < s) :
    Arithmetic.PrimeModels.ArithmeticPrimePELModels P := by
  have hδ : ∀ i, 0 < P.polarizationType i := by
    rcases hP with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩
    exact hpos
  apply Arithmetic.ModelsFromGraphFactory.arithmeticPrimePELModels_of_graph_factory P hP hs
  intro R _ _ p _ hp hpR h2R _hδR d hd hdR
  exact AbelianModuli.HilbertConstruction.Unit.GraphPowerLocusFactory.unitGraphPowerLocusFactory R (3 * s) p d P.polarizationType hd hδ hp hpR
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using h2R.mul hdR)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConcreteArithmeticPrimeModels
