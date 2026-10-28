import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource
import OAI.NumberTheory.ArithmeticGroups.CongruenceLevelDatum
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LatticeLevels

/-! # Reference Datum -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

noncomputable section

/-! The reference moduli input is obtained from the source's actual
Hermitian coefficient and complete set of archimedean places. CongruenceLevel is
an explicit named theorem input. No moduli model, Hecke action, or slope
conclusion is inserted into the source family. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

def embeddings (places : GeometricSource.CM.Places E) (i : Fin places.count) : E →ₐ[ℚ] ℂ :=
  ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (places.representative i)

theorem embeddings_complete (places : GeometricSource.CM.Places E) :
    Function.Bijective
      (fun p : Fin places.count × Bool =>
        if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (embeddings E places p.1)
        else embeddings E places p.1) := by
  have h := (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).bijective.comp places.complete
  convert h using 1
  funext p
  rcases p with ⟨i, b⟩
  cases b
  · rfl
  · exact (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation E _).symm

theorem embeddings_distinguished (places : GeometricSource.CM.Places E) :
    embeddings E places places.distinguished = E.val := by
  ext x
  simp only [embeddings, places.identity, ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_apply, AlgEquiv.one_apply]
  rfl

omit [IsGalois ℚ E] in
theorem representative_ne_id_conjugate (places : GeometricSource.CM.Places E)
    (i : Fin places.count) (hi : i ≠ places.distinguished) :
    places.representative i ≠ 1 ∧ places.representative i ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E := by
  constructor
  · intro h
    have he := places.complete.1 (a₁ := (i, false)) (a₂ := (places.distinguished, false))
      (by simpa only [Bool.false_eq_true, ite_false, places.identity] using h)
    exact hi (congrArg Prod.fst he)
  · intro h
    have he := places.complete.1 (a₁ := (i, false)) (a₂ := (places.distinguished, true))
      (by simpa only [Bool.false_eq_true, ite_false, ite_true, places.identity, mul_one] using h)
    exact hi (congrArg Prod.fst he)

theorem source_signature (B : GeometricSource.CM.BallDatum E) (places : GeometricSource.CM.Places E) :
    NumberField.IsCMField.complexConj E B.b = B.b ∧ B.b ≠ 0 ∧
      (embeddings E places places.distinguished B.b).re < 0 ∧
      ∀ i, i ≠ places.distinguished → 0 < (embeddings E places i B.b).re := by
  refine ⟨B.conjugate_b, ?_, ?_, ?_⟩
  · intro hzero
    have h := B.negative
    rw [hzero, IntermediateField.coe_zero, Complex.zero_re] at h
    exact (lt_irrefl 0) h
  · rw [embeddings_distinguished]
    exact B.negative
  · intro i hi
    obtain ⟨h1, hc⟩ := representative_ne_id_conjugate E places i hi
    exact B.definite (places.representative i) h1 hc

theorem source_degree (places : GeometricSource.CM.Places E) :
    0 < places.count ∧ Module.finrank ℚ E = 2 * places.count := by
  refine ⟨Nat.zero_lt_of_lt places.distinguished.isLt, ?_⟩
  have hc := Fintype.card_congr (Equiv.ofBijective _ places.complete)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hc
  rw [← IsGalois.card_aut_eq_finrank ℚ E, Nat.card_eq_fintype_card, ← hc]
  omega

/-- The complete CongruenceLevel proposition, in its checked analytic definitions. -/
def CongruenceLevelInput (s : ℕ) : Prop :=
  ∀ (σ : Fin s → E →ₐ[ℚ] ℂ)
    (_hσ : Function.Bijective (fun p : Fin s × Bool =>
      if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (μ : Fin s) (b : E)
    (_hb : NumberField.IsCMField.complexConj E b = b)
    (_hb_nonzero : b ≠ 0) (_hμ : (σ μ b).re < 0)
    (_hcompact : ∀ i, i ≠ μ → 0 < (σ i b).re) (dref : Fin s → Bool),
      NumberTheory.ArithmeticGroups.CongruenceLevelDatum.ReferenceDatum σ μ b dref

/-- Apply CongruenceLevel to the actual coefficient and place representatives of the
source ball. The reference compact signs can be chosen independently. -/
theorem reference_datum_from_source (B : GeometricSource.CM.BallDatum E) (places : GeometricSource.CM.Places E)
    (h_CongruenceLevel : CongruenceLevelInput E places.count) (dref : Fin places.count → Bool) :
    NumberTheory.ArithmeticGroups.CongruenceLevelDatum.ReferenceDatum (embeddings E places)
      places.distinguished B.b dref := by
  obtain ⟨hb, hb0, hμ, hc⟩ := source_signature E B places
  exact h_CongruenceLevel (embeddings E places) (embeddings_complete E places)
    places.distinguished B.b hb hb0 hμ hc dref

omit [IsGalois ℚ E] in
/-- The source and the reference theory use exactly the same principal
special-unitary condition when their lattice is the same. -/
theorem principalLevel_iff (B : GeometricSource.CM.BallDatum E) (N : ℕ) (g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E) :
    B.principalLevel N g ↔
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel B.b B.lattice N g ∧
        LinearMap.det g.toLinearMap = 1 := by
  constructor
  · rintro ⟨hh, hd, hl, hc⟩
    exact ⟨⟨hh, hl, hc⟩, hd⟩
  · rintro ⟨⟨hh, hl, hc⟩, hd⟩
    exact ⟨hh, hd, hl, hc⟩

omit [IsGalois ℚ E] in
/-- Every fixed reference level contains all sufficiently divisible source
levels. This applies to the full lattice produced by CongruenceLevel, without equating
its chosen lattice to the original one. -/
theorem source_levels_refine_reference (B : GeometricSource.CM.BallDatum E)
    (Λ : Submodule ℤ (GeometricSource.CM.Vec E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (N Nbase : ℕ) (hN : 0 < N) (hNbase : 0 < Nbase) :
    ∃ M : ℕ, 0 < M ∧ Nbase ∣ M ∧
      ∀ L : ℕ, M ∣ L → ∀ g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E,
        B.principalLevel L g →
          NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel B.b Λ N g ∧ LinearMap.det g.toLinearMap = 1 := by
  obtain ⟨M, hM, hbase, hlevels⟩ := LatticeLevels.CM.cofinal_principal_levels
    B.lattice Λ B.lattice_fg hΛ.1 B.lattice_full hΛ.2.1 N Nbase hN hNbase
  refine ⟨M, hM, hbase, ?_⟩
  intro L hL g hg
  have hprincipal := hlevels L hL (g.restrictScalars ℚ) ⟨hg.2.2.1, hg.2.2.2⟩
  exact ⟨⟨hg.1, hprincipal.1, hprincipal.2⟩, hg.2.1⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
