import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupCharacterBound
import OAI.AlgebraicGeometry.GroupSchemes.LikeCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableSubgroup

/-! # Hopf Subquotient Character Bound -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HopfSubquotientCharacterBound.Construction

noncomputable section

/-! Actual surjective and injective Hopf-coordinate maps supply the
cyclic subquotient bound for additive characters of a quotient group scheme. -/

open OAI.AlgebraicGeometry.GroupSchemes.LikeCharacters.FiniteEtale
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableSubgroup.CM

variable (k M R : Type) [Field k] [CommGroup M] [CommRing R] [HopfAlgebra k R]

def monoidAlgebraBasisCharacter : M →* GroupLike k (MonoidAlgebra k M) where
  toFun m := ⟨MonoidAlgebra.single m 1, MonoidAlgebra.isGroupLikeElem_single_one m⟩
  map_one' := by apply GroupLike.val_injective; rfl
  map_mul' x y := by
    apply GroupLike.val_injective
    change MonoidAlgebra.single (x * y) (1 : k) =
      MonoidAlgebra.single x (1 : k) * MonoidAlgebra.single y (1 : k)
    simp only [MonoidAlgebra.single_mul_single, one_mul]

theorem monoidAlgebraBasisCharacter_surjective :
    Function.Surjective (monoidAlgebraBasisCharacter k M) := by
  intro x
  obtain ⟨m, hm⟩ := MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one.mp x.isGroupLikeElem_val
  exact ⟨m, GroupLike.val_injective hm⟩

def monoidAlgebraQuotientCharacters (a : MonoidAlgebra k M →ₐc[k] R) : M →* GroupLike k R :=
  (GroupSchemes.LikeCharacters.FiniteEtale.groupLikeMap k (MonoidAlgebra k M) a).comp (monoidAlgebraBasisCharacter k M)

theorem monoidAlgebraQuotientCharacters_surjective
    (a : MonoidAlgebra k M →ₐc[k] R) (ha : Function.Surjective a) :
    Function.Surjective (monoidAlgebraQuotientCharacters k M R a) :=
  (GroupSchemes.LikeCharacters.FiniteEtale.groupLikeMap_surjective k (MonoidAlgebra k M) a ha (HodgeConjecture.HeckeCycles.DiagonalizableSubgroup.CM.monoidAlgebra_character_span k M)).comp
    (monoidAlgebraBasisCharacter_surjective k M)

theorem hopfCharacterMap_injective {B : Type} [CommRing B] [HopfAlgebra k B]
    (b : B →ₐc[k] R) (hb : Function.Injective b) :
    Function.Injective (GroupSchemes.LikeCharacters.FiniteEtale.groupLikeMap k B b) := by
  intro x y h
  apply GroupLike.val_injective
  exact hb (congrArg GroupLike.val h)

theorem hopfSubquotientCharacter_finrank_le
    {B : Type} [CommRing B] [HopfAlgebra k B] (m d : ℕ)
    (a : MonoidAlgebra k (Multiplicative (Fin d → ZMod m)) →ₐc[k] R)
    (ha : Function.Surjective a) (b : B →ₐc[k] R) (hb : Function.Injective b) :
    Module.finrank k (Additive (GroupLike k B) →+ k) ≤ d := by
  let r := monoidAlgebraQuotientCharacters k (Multiplicative (Fin d → ZMod m)) R a
  exact SubgroupCharacterBound.Construction.finiteCyclicSubgroupCharacter_finrank_le m d r.toAdditive
    (monoidAlgebraQuotientCharacters_surjective k _ R a ha)
    (GroupSchemes.LikeCharacters.FiniteEtale.groupLikeMap k B b).toAdditive (hopfCharacterMap_injective k R b hb)

theorem hopfSubquotientCharacter_finrank_le_of_labels
    {B : Type} [CommRing B] [HopfAlgebra k B] (m d : ℕ)
    (e : M ≃* Multiplicative (Fin d → ZMod m))
    (a : MonoidAlgebra k M →ₐc[k] R) (ha : Function.Surjective a)
    (b : B →ₐc[k] R) (hb : Function.Injective b) :
    Module.finrank k (Additive (GroupLike k B) →+ k) ≤ d := by
  let r := (monoidAlgebraQuotientCharacters k M R a).comp e.symm.toMonoidHom
  exact SubgroupCharacterBound.Construction.finiteCyclicSubgroupCharacter_finrank_le m d r.toAdditive
    ((monoidAlgebraQuotientCharacters_surjective k M R a ha).comp e.symm.surjective)
    (GroupSchemes.LikeCharacters.FiniteEtale.groupLikeMap k B b).toAdditive (hopfCharacterMap_injective k R b hb)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HopfSubquotientCharacterBound.Construction
