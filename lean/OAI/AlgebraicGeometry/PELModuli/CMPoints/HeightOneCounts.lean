import OAI.AlgebraicGeometry.GroupSchemes.Classification
import OAI.AlgebraicGeometry.GroupSchemes.LikeCharacters
import Mathlib.Algebra.CharP.Reduced

/-! # Height One Counts -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HeightOneCounts

noncomputable section

section

/-! Point and character counts for the actual height-one FiniteEtale towers.
Their product is the finite-level rank. This is the numerical ingredient
for ordinary CM specialization once the full CM factors are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry WithConv
open scoped _root_.CategoryTheory.MonObj

section Characters

variable {k A B : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
  [CommRing B] [Algebra k B]

theorem groupLike_convolution_power (c : GroupLike k A) (f : WithConv (A →ₐ[k] B)) (n : ℕ) :
    (f ^ n).ofConv c.val = (f.ofConv c.val) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, AlgHom.convOne_apply, c.isGroupLikeElem_val.counit_eq_one, map_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, AlgHom.convMul_apply, c.isGroupLikeElem_val.comul_eq_tmul_self]
    simpa using congrArg (fun x => x * f.ofConv c.val) ih

end Characters

variable {k : Type} [Field k] [IsAlgClosed k] {q : ℕ} [Fact q.Prime] [CharP k q]
  (G : GroupSchemes.FiniteEtale.PDivisibleGroup k q 1)

omit [IsAlgClosed k] [Fact q.Prime] [CharP k q] in
theorem heightOne_character_value_power (n : ℕ) (c : (G.level n).characterGroup) :
    (G.level n).characterValue c ^ (q ^ n) = 1 := by
  let A := (G.level n).algebra
  let : Algebra k A := (G.level n).coordinateHopf.toAlgebra
  let := (G.level n).coordinateHopf
  let e := (G.level n).coordinatePoints A
  let f : WithConv (A →ₐ[k] A) := toConv (AlgHom.id k A)
  have hp : f ^ (q ^ n) = 1 := by
    apply e.injective
    exact (map_pow e f (q ^ n)).trans ((G.annihilated k n A (e f)).trans e.map_one.symm)
  have h := groupLike_convolution_power (show GroupLike k A from c) f (q ^ n)
  rw [hp, AlgHom.convOne_apply, (show GroupLike k A from c).isGroupLikeElem_val.counit_eq_one,
    map_one] at h
  exact h.symm

omit [IsAlgClosed k] in
theorem heightOne_character_eq_one_of_split (n : ℕ)
    (hsplit : Algebra.IsFiniteSplit k (G.level n).algebra) (c : (G.level n).characterGroup) : c = 1 := by
  let A := (G.level n).algebra
  let : Algebra.IsFiniteSplit k A := hsplit
  let : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  have hi : Function.Injective (algebraMap k A) := by
    apply Function.LeftInverse.injective (g := (G.level n).coordinateAugmentation)
    intro x
    exact (G.level n).coordinateAugmentation.commutes x
  let : ExpChar A q := expChar_of_injective_algebraMap hi q
  have hc := heightOne_character_value_power G n c
  have he : (G.level n).characterValue c = 1 := by
    apply (iterateFrobenius_inj A q n)
    change (G.level n).characterValue c ^ (q ^ n) = 1 ^ (q ^ n)
    exact hc.trans (one_pow _).symm
  exact GroupLike.val_injective he

theorem heightOne_point_character_card (n : ℕ) :
    Nat.card (G.level n).rationalPoints * Nat.card (G.level n).characterGroup = q ^ n := by
  rcases G.first_local_or_split with hlocal | hsplit
  · let : IsLocalRing (G.level n).algebra := G.local_of_first_local hlocal n
    let : Subsingleton (G.level n).rationalPoints :=
      ⟨fun x y => ((G.level n).point_eq_one_of_local x).trans
        ((G.level n).point_eq_one_of_local y).symm⟩
    let : Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra := G.dual_split_of_first_local hlocal n
    rw [Nat.card_unique (α := (G.level n).rationalPoints), one_mul,
      (G.level n).characterGroup_card, G.rank, Nat.mul_one]
  · have hs := G.split_of_first_split hsplit n
    let : Algebra.IsFiniteSplit k (G.level n).algebra := hs
    let : Subsingleton (G.level n).characterGroup :=
      ⟨fun x y => (heightOne_character_eq_one_of_split G n hs x).trans
        (heightOne_character_eq_one_of_split G n hs y).symm⟩
    rw [Nat.card_unique (α := (G.level n).characterGroup), mul_one,
      (G.level n).rationalPoints_card, G.rank, Nat.mul_one]

end

/-! A self-dual finite product of height-one factors has the ordinary
geometric point count. The point and character identifications are
actual equivalences; the count follows from FiniteEtale and finite products. -/

variable {k I : Type} {X Y : Type*} [Field k] [IsAlgClosed k] [Fintype I]
  {q : ℕ} [Fact q.Prime] [CharP k q]

theorem heightOne_product_point_character_card
    (G : I → GroupSchemes.FiniteEtale.PDivisibleGroup k q 1) (n : ℕ) :
    Nat.card (∀ i, ((G i).level n).rationalPoints) *
        Nat.card (∀ i, ((G i).level n).characterGroup) = q ^ (n * Fintype.card I) := by
  rw [Nat.card_pi, Nat.card_pi, ← Finset.prod_mul_distrib]
  simp only [heightOne_point_character_card, Finset.prod_const, Finset.card_univ, ← pow_mul]

theorem ordinary_count_of_selfDual_heightOne_factors
    (G : I → GroupSchemes.FiniteEtale.PDivisibleGroup k q 1) (g : ℕ)
    (hI : Fintype.card I = 2 * g)
    (ep : X ≃ (∀ i, ((G i).level 1).rationalPoints))
    (ec : Y ≃ (∀ i, ((G i).level 1).characterGroup)) (ed : X ≃ Y) :
    Nat.card X = q ^ g := by
  have h := heightOne_product_point_character_card G 1
  rw [← Nat.card_congr ep, ← Nat.card_congr ec, ← Nat.card_congr ed,
    Nat.one_mul, hI] at h
  have hs : Nat.card X ^ 2 = (q ^ g) ^ 2 := by
    rw [pow_two, h, ← pow_mul, Nat.mul_comm g 2]
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) hs

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HeightOneCounts
