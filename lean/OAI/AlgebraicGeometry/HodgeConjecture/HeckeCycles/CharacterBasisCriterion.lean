import OAI.AlgebraicGeometry.Picard.Homomorphisms.ElementaryCharacters

/-! # Character Basis Criterion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CharacterBasisCriterion.CM

noncomputable section

/-! An injective family of Hopf characters with cardinality equal to
the coordinate rank supplies a basis and the actual diagonalizable group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.ElementaryCharacters.Construction

universe u
variable (k R : Type u) [Field k] [CommRing R] [HopfAlgebra k R] [Module.Finite k R]
  (I : Type u) [CommGroup I] [Finite I]
  (f : I →* GroupLike k R) (hf : Function.Injective f)
  (hrank : Module.finrank k R = Nat.card I)

include hf hrank in
omit [Finite I] in
theorem character_card : Nat.card (GroupLike k R) = Module.finrank k R := by
  let : Finite (GroupLike k R) := Picard.Homomorphisms.CharacterSpan.Construction.finite_coordinateCharacters k R
  let := Fintype.ofFinite (GroupLike k R)
  apply Nat.le_antisymm
  · simpa only [Nat.card_eq_fintype_card] using
      (linearIndep_groupLikeVal (R := k) (A := R)).fintype_card_le_finrank
  · exact hrank.trans_le (Nat.card_le_card_of_injective f hf)

def characterEquiv : I ≃* GroupLike k R := by
  let : Finite (GroupLike k R) := Picard.Homomorphisms.CharacterSpan.Construction.finite_coordinateCharacters k R
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, hrank.symm.trans (character_card k R I f hf hrank).symm⟩)

def diagonalizableIso :
    (hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k R)) ≅
      (hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k (MonoidAlgebra k I))) :=
  Picard.Homomorphisms.ElementaryCharacters.Construction.diagonalizableGroupIsoOfCharacterCard k R (character_card k R I f hf hrank) ≪≫
    (hopfSpec (.of k)).mapIso (CommHopfAlgCat.isoMk
      (MonoidAlgebra.domCongrBialgEquiv k k (characterEquiv k R I f hf hrank))).op

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CharacterBasisCriterion.CM
