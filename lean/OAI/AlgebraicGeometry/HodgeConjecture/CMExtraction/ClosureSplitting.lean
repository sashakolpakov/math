import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaloisDiscrete
import OAI.NumberTheory.PadicHodge.Arithmetic

/-! # Closure Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices

noncomputable section

/-! Extend the actual native local embedding through any fixed algebraic
embedding of E. The resulting canonical global valuation satisfies GaloisValuation's
complete splitting formula, with no valuation-normalization hypothesis. -/

open _root_.NumberField IsDedekindDomain
open OAI.NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter
open scoped WithZero Classical

def extendAlgebraicEmbedding {E F : Type} [Field E] [NumberField E]
    [Field F] [CharZero F] [IsAlgClosed F]
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (f : E →+* F) : ParameterChoices.Qbar →+* F := by
  let : Algebra.IsAlgebraic ℚ ParameterChoices.Qbar := AlgebraicClosure.isAlgebraic ℚ
  let : Algebra E ParameterChoices.Qbar := ιE.toAlgebra
  let : IsScalarTower ℚ E ParameterChoices.Qbar := IsScalarTower.of_algebraMap_eq
    (fun x => (ιE.commutes x).symm)
  let : Algebra.IsAlgebraic E ParameterChoices.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let : Algebra E F := f.toAlgebra
  exact (IsAlgClosed.lift : ParameterChoices.Qbar →ₐ[E] F).toRingHom

theorem extendAlgebraicEmbedding_spec {E F : Type} [Field E] [NumberField E]
    [Field F] [CharZero F] [IsAlgClosed F]
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (f : E →+* F) (x : E) :
    extendAlgebraicEmbedding ιE f (ιE x) = f x := by
  let : Algebra.IsAlgebraic ℚ ParameterChoices.Qbar := AlgebraicClosure.isAlgebraic ℚ
  let : Algebra E ParameterChoices.Qbar := ιE.toAlgebra
  let : IsScalarTower ℚ E ParameterChoices.Qbar := IsScalarTower.of_algebraMap_eq
    (fun x => (ιE.commutes x).symm)
  let : Algebra.IsAlgebraic E ParameterChoices.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let : Algebra E F := f.toAlgebra
  exact (IsAlgClosed.lift : ParameterChoices.Qbar →ₐ[E] F).commutes x

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)

def nativeClosureEmbedding (i : Fin s × Bool) : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q] :=
  extendAlgebraicEmbedding ιE
    ((algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i))

theorem nativeClosureEmbedding_spec (i : Fin s × Bool) (x : E) :
    nativeClosureEmbedding D ιE i (ιE x) =
      algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i x) :=
  extendAlgebraicEmbedding_spec ιE _ x

theorem nativeGlobalValuation_on_field (i : Fin s × Bool) (x : E) :
    NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (nativeClosureEmbedding D ιE i) (ιE x) =
      ((LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i x).valuation : ℚ) := by
  rw [NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation, nativeClosureEmbedding_spec]
  exact NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_algebraMap q _

theorem exists_native_GaloisValuation_splitting
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    (hq : D.IsGoodCompletelySplitPrime) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    (v : Fin s) (side : Bool) :
    ∃ (r : Eˣ) (M : ℕ), 0 < M ∧
      (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
      (∀ τ : Gal(E/ℚ),
        NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (nativeClosureEmbedding D ιE (v, side)) (ιE (τ (r : E))) =
          if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 E))) (depth : HeightOneSpectrum (𝓞 E) → ℕ),
        Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (v, side) ∉ S → Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (v, !side) ∉ S →
        ∃ N : ℕ, 0 < N ∧ ∀ p ∈ S,
          p.valuation E ((r : E) ^ N - 1) ≤ WithZero.exp (-(depth p : ℤ))) := by
  classical
  obtain ⟨r, M, hM, hnorm, hval, happrox⟩ := GaloisDiscrete.ParameterChoices.exists_native_scalar_galois D hg hq v side
  refine ⟨r, M, hM, hnorm, ?_, happrox⟩
  intro τ
  rw [nativeGlobalValuation_on_field]
  change ((LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (v, side) (τ (r : E))).valuation : ℚ) =
    if τ = (NumberField.IsCMField.complexConj E).restrictScalars ℚ then (M : ℚ)
    else if τ = 1 then -(M : ℚ) else 0
  rw [hval τ]
  split_ifs <;> simp only [Int.cast_natCast, Int.cast_neg, Int.cast_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices
