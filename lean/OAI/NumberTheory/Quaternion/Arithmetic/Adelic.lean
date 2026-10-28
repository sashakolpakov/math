import OAI.NumberTheory.Quaternion.Arithmetic.AdelicGroup
import OAI.NumberTheory.Quaternion.Arithmetic.OpenSubgroupQuotient
import OAI.NumberTheory.Quaternion.Arithmetic.CompactQuotientProjection

/-! # Adelic -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Adelic

noncomputable section

/-! Compact full adelic quotients give compact quotients by the
actual S-integral rational subgroup in each finite local product. -/

open scoped Classical
open Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def sIntegralFullAdelicMap (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    Groups.sIntegralPoints G (S : Set (LocalAdeles.Place F)) →* AdelicGroup.fullAdelicIntegralOutside G S where
  toFun q := ⟨AdelicGroup.diagonalFullAdelic G q.val, (AdelicGroup.diagonalFullAdelic_mem_integralOutside G S q.val).mpr q.property⟩
  map_one' := Subtype.ext (map_one (AdelicGroup.diagonalFullAdelic G))
  map_mul' q r := Subtype.ext (map_mul (AdelicGroup.diagonalFullAdelic G) q.val r.val)

theorem sIntegralFullAdelicMap_range (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    (sIntegralFullAdelicMap G S).range =
      (AdelicGroup.diagonalFullAdelic G).range.subgroupOf (AdelicGroup.fullAdelicIntegralOutside G S) := by
  ext z
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.val, congrArg Subtype.val hq⟩
  · rintro ⟨q, hq⟩
    have hmem : q ∈ Groups.sIntegralPoints G (S : Set (LocalAdeles.Place F)) :=
      (AdelicGroup.diagonalFullAdelic_mem_integralOutside G S q).mp (hq.symm ▸ z.property)
    exact ⟨⟨q, hmem⟩, Subtype.ext hq⟩

def sArithmeticLocalSubgroup (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    Subgroup (Ambient.OmittedLocalProduct G S) :=
  ((AdelicGroup.integralOutsideProjection G S).comp (sIntegralFullAdelicMap G S)).range

theorem sArithmeticLocalSubgroup_mem (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (y : Ambient.OmittedLocalProduct G S) : y ∈ sArithmeticLocalSubgroup G S ↔
      ∃ q : G.RationalPoints, q ∈ Groups.sIntegralPoints G (S : Set (LocalAdeles.Place F)) ∧
        ∀ v : (S : Set (LocalAdeles.Place F)), LocalAdeles.diagonalLocal G v.val q = y v := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q.val, q.property, ?_⟩
    intro v
    have he := congrFun hq v
    change AdelicGroup.fullAdelicEvaluation G v.val (AdelicGroup.diagonalFullAdelic G q.val) = y v at he
    rwa [AdelicGroup.fullAdelicEvaluation_diagonal] at he
  · rintro ⟨q, hq, he⟩
    refine ⟨⟨q, hq⟩, ?_⟩
    funext v
    exact (AdelicGroup.fullAdelicEvaluation_diagonal G v.val q).trans (he v)

theorem sArithmeticLocalSubgroup_eq_projection (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    ((AdelicGroup.diagonalFullAdelic G).range.subgroupOf (AdelicGroup.fullAdelicIntegralOutside G S)).map
      (AdelicGroup.integralOutsideProjection G S) = sArithmeticLocalSubgroup G S := by
  rw [← sIntegralFullAdelicMap_range, MonoidHom.map_range]
  rfl

theorem compact_sArithmeticLocal_quotient_of_full (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    [CompactSpace (AdelicGroup.FullAdelicGroupPoints G ⧸ (AdelicGroup.diagonalFullAdelic G).range)] :
    CompactSpace (Ambient.OmittedLocalProduct G S ⧸ sArithmeticLocalSubgroup G S) := by
  let : CompactSpace (AdelicGroup.fullAdelicIntegralOutside G S ⧸
      (AdelicGroup.diagonalFullAdelic G).range.subgroupOf (AdelicGroup.fullAdelicIntegralOutside G S)) :=
    OpenSubgroupQuotient.compact_open_subgroup_quotient (AdelicGroup.fullAdelicIntegralOutside G S) (AdelicGroup.diagonalFullAdelic G).range
      (AdelicGroup.fullAdelicIntegralOutside_isOpen G S)
  exact CompactQuotientProjection.compact_quotient_of_surjective (AdelicGroup.integralOutsideProjection G S)
    (AdelicGroup.integralOutsideProjection_continuous G S) (AdelicGroup.integralOutsideProjection_surjective G S)
    _ _ (sArithmeticLocalSubgroup_eq_projection G S).le

end

end OAI.NumberTheory.Quaternion.Arithmetic.Adelic
