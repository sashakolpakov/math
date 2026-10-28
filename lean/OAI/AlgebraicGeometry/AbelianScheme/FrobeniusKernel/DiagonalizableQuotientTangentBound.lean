import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HopfMap
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HopfSubquotientCharacterBound
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DiagonalizableSubquotientLieBound

/-! # Diagonalizable Quotient Tangent Bound -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DiagonalizableQuotientTangentBound.Construction

noncomputable section

/-! A flat quotient of a closed subgroup of d cyclic multiplicative
factors has tangent rank at most d, when the target is itself a closed
subgroup of a diagonalizable group. All inclusions and covers are native maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableSubgroup.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank.CM

variable {k : Type} [Field k]
variable (G H : Grp (Over (Spec (.of k))))
  [IsFinite G.X.hom] [IsFinite H.X.hom] [IsCommMonObj G.X] [IsCommMonObj H.X]
variable (M I : Type) [CommGroup M] [CommGroup I]
variable (iG : G ⟶ (hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k (MonoidAlgebra k M))))
  (iH : H ⟶ (hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k (MonoidAlgebra k I))))
  [IsClosedImmersion iG.hom.hom.left] [IsClosedImmersion iH.hom.hom.left]
variable (f : G ⟶ H) [Flat f.hom.hom.left] [Surjective f.hom.hom.left]

include iG iH f in
theorem diagonalizable_quotient_tangentRank_le (m d : ℕ)
    (labels : M ≃* Multiplicative (Fin d → ZMod m)) :
    ∃ r ≤ d, HodgeConjecture.HeckeCycles.TangentRank.CM.HasRank H r := by
  obtain ⟨R, hR, _, ⟨eR⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  obtain ⟨B, hB, ⟨eB⟩, hspan⟩ := HodgeConjecture.HeckeCycles.DiagonalizableSubgroup.CM.spanning_presentation_of_closed_embedding k H I iH
  let : Module.Finite k R := hR
  let : Module.Finite k B := hB
  let : Finite (GroupLike k B) := Picard.Homomorphisms.CharacterSpan.Construction.finite_coordinateCharacters k B
  let v := eR.hom ≫ iG
  let w := eR.hom ≫ f ≫ eB.inv
  have : IsIso eR.hom.hom.hom.left :=
    ((Grp.forget (Over (Spec (.of k)))) ⋙ Over.forget (Spec (.of k))).map_isIso eR.hom
  have : IsIso eB.inv.hom.hom.left :=
    ((Grp.forget (Over (Spec (.of k)))) ⋙ Over.forget (Spec (.of k))).map_isIso eB.inv
  have : IsClosedImmersion v.hom.hom.left := inferInstanceAs
    (IsClosedImmersion (eR.hom.hom.hom.left ≫ iG.hom.hom.left))
  have : Flat w.hom.hom.left := inferInstanceAs
    (Flat (eR.hom.hom.hom.left ≫ f.hom.hom.left ≫ eB.inv.hom.hom.left))
  have : Surjective w.hom.hom.left := inferInstanceAs
    (Surjective (eR.hom.hom.hom.left ≫ f.hom.hom.left ≫ eB.inv.hom.hom.left))
  let a := (HopfMap.Construction.nativeHopfCoordinateMap v).hom
  let b := (HopfMap.Construction.nativeHopfCoordinateMap w).hom
  have hr : Module.finrank k (Additive (GroupLike k B) →+ k) ≤ d :=
    HopfSubquotientCharacterBound.Construction.hopfSubquotientCharacter_finrank_le_of_labels k M R m d labels a
      (HopfMap.Construction.nativeHopfCoordinateMap_surjective v) b (HopfMap.Construction.nativeHopfCoordinateMap_injective w)
  let e := eB.symm ≪≫ (hopfSpec (.of k)).mapIso
    (CommHopfAlgCat.isoMk (Picard.Homomorphisms.CharacterSpan.Construction.characterHopfEquivOfSpan k B hspan)).op
  exact ⟨Module.finrank k (Additive (GroupLike k B) →+ k), hr,
    HodgeConjecture.HeckeCycles.TangentRank.CM.rank_transport e.symm (DiagonalizableSubquotientLieBound.Construction.diagonalizable_character_tangentRank (k := k) (M := GroupLike k B))⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DiagonalizableQuotientTangentBound.Construction
