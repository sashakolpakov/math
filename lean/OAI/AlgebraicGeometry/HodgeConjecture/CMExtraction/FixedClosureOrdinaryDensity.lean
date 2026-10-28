import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosureOrdinaryPrime
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryReduction

/-! # Fixed Closure Ordinary Density -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosureOrdinaryDensity.Ordinary

noncomputable section

/-! Retain the selected complex and local closure embeddings in the full
ordinary reduction, including density, height, duality and Lie-rank clauses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryReduction

theorem exists_fixed_closure_dense_ordinary
    (hOpenness : PELModuli.CMPoints.OrdinaryReduction.OpennessInput) (hSplitPrimes : PELModuli.CMPoints.Arithmetic.SplitPrimesInput)
    (hHilb : PELModuli.IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : PELModuli.IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hCMAbelianVarietyA : PELModuli.CMPoints.Descent.AbelianInput) (hCMAbelianVarietyM : PELModuli.CMPoints.Descent.ModuliInput)
    (E K : Type) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {Idx : Type} [Fintype Idx]
    (L : Idx → Type) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt K q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∀ (jC : ParameterChoices.Qbar →+* ℂ) (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]),
      ∃ j : M.QadicChoice q,
        j.complexClosure = jC ∧ j.iota = ι ∧
        j.fieldInClosure = (CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC M.arithmetic.embedding).toRingHom ∧
        j.HasSplitCoordinates M.extendedEmbedding ∧
        ∃ R : M.GoodIntegralReduction q j,
          (∀ a : M.Family, IsOpen (R.ordinaryLocus a) ∧
            ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val}) ∧
          ∃ chosen : Set Gal(E/ℚ),
            let c := (NumberField.IsCMField.complexConj E).restrictScalars ℚ
            c ∈ chosen ∧ (∀ τ, τ ∈ chosen ↔ c * τ ∉ chosen) ∧
            (∀ (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)),
              R.HasHeight a x τ 3 ∧ R.PolarizationDuality a x τ (c * τ)) ∧
            (∀ (a : M.Family) (x : R.geom a),
              R.HasLieRank a x c 1 ∧
              ∀ τ ∈ chosen, τ ≠ c → R.HasLieRank a x τ 0 ∨ R.HasLieRank a x τ 3) := by
  obtain ⟨D, hD⟩ := M.exists_reduction_height_bound hM
  obtain ⟨q, hq, hb, hx, hE, hK, hBase, hL, hchoices⟩ :=
    FixedClosureOrdinaryPrime.Ordinary.exists_fixed_closure_ordinary_component_prime hSplitPrimes hHilb hEnd hCMAbelianVarietyA hCMAbelianVarietyM
      M hM L excluded (max bound D)
  let : Fact q.Prime := ⟨hq⟩
  refine ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx, hE, hK, hBase, hL, ?_⟩
  intro jC ι
  obtain ⟨j, hJC, hJI, hJF, hsplit, R, hpoints⟩ := hchoices jC ι
  choose y hy using hpoints
  obtain ⟨chosen, hc, hp, hlie⟩ := R.exists_representatives_with_lieRanks hM
  refine ⟨j, hJC, hJI, hJF, hsplit, R,
    fun a => ⟨R.ordinaryLocus_open hOpenness a,
      PELModuli.CMPoints.OrdinaryReduction.ordinary_dense_of_finite_component_points hOpenness hM R a (y a) (hy a)⟩,
    chosen, hc, hp, ?_, hlie⟩
  intro a x τ
  exact ⟨hD q hq j hsplit (lt_of_le_of_lt (le_max_right _ _) hb) R a x τ,
    R.fiber_polarization_duality hsplit a x τ⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosureOrdinaryDensity.Ordinary
