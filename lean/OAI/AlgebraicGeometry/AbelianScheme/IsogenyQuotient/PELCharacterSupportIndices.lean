import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis

/-! # PEL Character Support Indices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELCharacterSupportIndices.Construction

noncomputable section

/-! The original rank-three signature leaves only its distinguished
two-by-one pair available to a form supported on conjugate characters.
The index sets and their cardinalities use the actual prescribed ranks. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

abbrev pelConormalBasisIndex := Σ j, Fin (P.pairedLieRank j)

def pelCharacterIndexEmbedding (q : Fin s × Bool) :
    Fin (P.pairedLieRank q) ↪ pelConormalBasisIndex P where
  toFun := fun i => ⟨q, i⟩
  inj' := by
    intro i j h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

def pelCharacterIndexSet (q : Fin s × Bool) : Finset (pelConormalBasisIndex P) :=
  Finset.univ.map (pelCharacterIndexEmbedding P q)

omit [NumberField E] [NumberField.IsCMField E] in
theorem mem_pelCharacterIndexSet (q : Fin s × Bool) (i : pelConormalBasisIndex P) :
    i ∈ pelCharacterIndexSet P q ↔ i.1 = q := by
  classical
  constructor
  · intro hi
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
    exact (congrArg Sigma.fst hj).symm
  · rcases i with ⟨p, j⟩
    intro hp
    change p = q at hp
    subst p
    exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩

omit [NumberField E] [NumberField.IsCMField E] in
theorem pelCharacterIndexSet_card (q : Fin s × Bool) :
    (pelCharacterIndexSet P q).card = P.pairedLieRank q := by
  rw [pelCharacterIndexSet, Finset.card_map, Finset.card_univ, Fintype.card_fin]

def pelPositiveTangentIndices := pelCharacterIndexSet P (P.distinguished, false)
def pelNegativeTangentIndices := pelCharacterIndexSet P (P.distinguished, true)

omit [NumberField E] [NumberField.IsCMField E] in
theorem pelPositiveTangentIndices_card : (pelPositiveTangentIndices P).card = 2 := by
  rw [pelPositiveTangentIndices, pelCharacterIndexSet_card]
  simp [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.pairedLieRank, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank]

omit [NumberField E] [NumberField.IsCMField E] in
theorem pelNegativeTangentIndices_card : (pelNegativeTangentIndices P).card = 1 := by
  rw [pelNegativeTangentIndices, pelCharacterIndexSet_card]
  simp [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.pairedLieRank, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank]

omit [NumberField E] [NumberField.IsCMField E] in
theorem pelConjugateIndices_distinguished (i j : pelConormalBasisIndex P)
    (h : i.1 = (j.1.1, !j.1.2)) :
    (i ∈ pelPositiveTangentIndices P ∧ j ∈ pelNegativeTangentIndices P) ∨
      (i ∈ pelNegativeTangentIndices P ∧ j ∈ pelPositiveTangentIndices P) := by
  classical
  rcases i with ⟨⟨a, b⟩, x⟩
  rcases j with ⟨⟨c, d⟩, y⟩
  have ha : a = c := congrArg Prod.fst h
  subst a
  have hc : c = P.distinguished := by
    by_contra hn
    have hx := x.isLt
    have hy := y.isLt
    cases b <;> cases d <;> cases hs : P.compactSigns c <;>
      simp_all [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.pairedLieRank, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank]
  simp only [pelPositiveTangentIndices, pelNegativeTangentIndices, mem_pelCharacterIndexSet]
  cases b <;> cases d <;> simp_all

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELCharacterSupportIndices.Construction
