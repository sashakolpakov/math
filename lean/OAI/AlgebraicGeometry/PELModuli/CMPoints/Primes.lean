import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryReduction
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Open
import OAI.NumberTheory.Splitting.SplitPrimes
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Hom
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismEquationLoci

/-! # Primes -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Primes.Core

noncomputable section

section

/-! The four exact inputs of the accepted CMPoints construction, now proved.
The ordinary and splitting predicates are definitionally the same geometric
fiber and residue-ring predicates. The Presentations terms retain the complete original
relative Hilbert/Hom and proper-source equation-locus specifications.
-/

theorem ordinary_openness : OrdinaryReduction.OpennessInput := by
  exact ArithmeticGeometry.OrdinaryLocus.Openness.Open.Construction.isOpen_ordinaryLocus

theorem completely_split_primes : Arithmetic.SplitPrimesInput := by
  exact NumberTheory.Splitting.SplitPrimes.Construction.chebotarev_splitting

theorem relative_hilbert_hom : IntegralModel.Presentations.Hilbert.HilbertHomInput := by
  exact HilbertScheme.Presentations.Relative.Hom.Core.relative_hilbert_and_hom_loci

theorem endomorphism_equations : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput := by
  exact HilbertScheme.Presentations.EndomorphismEquationLoci.Core.endomorphism_equation_loci

end

/-! The full frozen CMPoints result, with all four external result inputs discharged. -/

open OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryReduction

/-- CMPoints: arbitrarily good completely split primes with dense ordinary
locus on every geometric component of every universal family. -/
theorem exists_completely_split_prime_dense_ordinary
    (E K : Type) [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K]
    (M : Models.RankThreePELModel E K)
    (hM : M.HasPrescribedBallPeriods)
    {ι : Type*} [Fintype ι]
    (L : ι → Type*) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧
      Arithmetic.SplitsCompletelyAt E q ∧
      Arithmetic.SplitsCompletelyAt K q ∧
      Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ j : M.QadicChoice q,
        j.HasSplitCoordinates M.extendedEmbedding ∧
        ∃ R : M.GoodIntegralReduction q j,
          (∀ a : M.Family,
            IsOpen (R.ordinaryLocus a) ∧
            ∀ x : R.geom a,
              Dense {y : connectedComponent x | R.IsOrdinary a y.val}) ∧
          ∃ chosen : Set Gal(E/ℚ),
            let c : Gal(E/ℚ) :=
              (NumberField.IsCMField.complexConj E).restrictScalars ℚ
            c ∈ chosen ∧
            (∀ τ, τ ∈ chosen ↔ c * τ ∉ chosen) ∧
            (∀ (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)),
              R.HasHeight a x τ 3 ∧ R.PolarizationDuality a x τ (c * τ)) ∧
            (∀ (a : M.Family) (x : R.geom a),
              R.HasLieRank a x c 1 ∧
              ∀ τ ∈ chosen, τ ≠ c →
                R.HasLieRank a x τ 0 ∨ R.HasLieRank a x τ 3) := by
  exact OrdinaryReduction.exists_completely_split_prime_dense_ordinary
    ordinary_openness completely_split_primes relative_hilbert_hom endomorphism_equations
    E K M hM L excluded bound

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Primes.Core
