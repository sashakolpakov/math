import OAI.AlgebraicGeometry.GroupSchemes.LikeCharacters
import OAI.AlgebraicGeometry.GroupSchemes.DualCyclic

/-! # Character Generators -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! Compatible generators of coordinate characters in the multiplicative branch. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

namespace CharacterGenerators.FiniteEtale

universe u

/-- Generators lift along a surjection between cyclic groups of consecutive prime-power orders. -/
theorem generator_lift {A B : Type u} [CommGroup A] [CommGroup B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (n : ℕ) (f : A →* B) (hf : Function.Surjective f)
    (z : A) (hz : orderOf z = p ^ (n + 1)) (hA : Nat.card A = p ^ (n + 1))
    (hB : Nat.card B = p ^ n) (x : B) (hx : orderOf x = p ^ n) :
    ∃ y : A, orderOf y = p ^ (n + 1) ∧ f y = x := by
  have hgen : ∀ a : A, a ∈ Subgroup.zpowers z := by
    have ht : Subgroup.zpowers z = ⊤ := (Subgroup.card_eq_iff_eq_top _).mp
      (by rw [Nat.card_zpowers, hz, hA])
    intro a
    rw [ht]
    trivial
  have hfg : ∀ b : B, b ∈ Subgroup.zpowers (f z) := by
    intro b
    obtain ⟨a, rfl⟩ := hf b
    obtain ⟨m, rfl⟩ := hgen a
    exact ⟨m, (map_zpow f z m).symm⟩
  have hfz : orderOf (f z) = p ^ n := (orderOf_eq_card_of_forall_mem_zpowers hfg).trans hB
  cases n with
  | zero =>
    refine ⟨z, hz, ?_⟩
    have h1 : f z = 1 := orderOf_eq_one_iff.mp (by simpa only [pow_zero] using hfz)
    have h2 : x = 1 := orderOf_eq_one_iff.mp (by simpa only [pow_zero] using hx)
    exact h1.trans h2.symm
  | succ n =>
    obtain ⟨a, ha⟩ := (mem_powers_iff_mem_zpowers.mpr (hfg x))
    change f z ^ a = x at ha
    have hdiv : p ^ (n + 1) / (p ^ (n + 1)).gcd a = p ^ (n + 1) := by
      calc
        _ = orderOf (f z ^ a) := by rw [orderOf_pow, hfz]
        _ = p ^ (n + 1) := (congrArg orderOf ha).trans hx
    have hcop : (p ^ (n + 1)).Coprime a := by
      apply Nat.coprime_iff_gcd_eq_one.mpr
      have hpos : 0 < p ^ (n + 1) := pow_pos (Fact.out : p.Prime).pos _
      have heq := (Nat.div_eq_iff_eq_mul_left
        (Nat.gcd_pos_of_pos_left a hpos) (Nat.gcd_dvd_left _ _)).mp hdiv
      nlinarith
    have hcop' : (p ^ (n + 1 + 1)).Coprime a :=
      ((Nat.coprime_pow_left_iff (by omega) p a).mp hcop).pow_left _
    refine ⟨z ^ a, ?_, ?_⟩
    · rw [orderOf_pow, hz, hcop'.gcd_eq_one, Nat.div_one]
    · exact (map_pow f z a).trans ha

end CharacterGenerators.FiniteEtale

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- A coordinate character of full order. -/
def FiniteEtale.PDivisibleGroup.CharacterGenerator (G : FiniteEtale.PDivisibleGroup k p 1) (n : ℕ) :=
  { x : (G.level n).characterGroup // orderOf x = p ^ n }

/-- Every level admits a full-order coordinate character when the dual levels split. -/
theorem FiniteEtale.PDivisibleGroup.exists_character_order (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra) (n : ℕ) :
    ∃ x : (G.level n).characterGroup, orderOf x = p ^ n := by
  obtain ⟨x, hx⟩ := G.exists_dual_point_order hsplit n
  refine ⟨(G.level n).dualPointsCharacterEquiv x, ?_⟩
  exact (orderOf_injective (G.level n).dualPointsCharacterEquiv.toMonoidHom
    (G.level n).dualPointsCharacterEquiv.injective x).trans hx

/-- Full-order coordinate characters lift through each original inclusion. -/
theorem FiniteEtale.PDivisibleGroup.character_generator_lift (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra)
    (n : ℕ) (x : G.CharacterGenerator n) :
    ∃ y : G.CharacterGenerator (n + 1),
      FiniteEtale.FiniteCommGroupScheme.characterMap (G.inclusion n) y.val = x.val := by
  have := hsplit n
  have := hsplit (n + 1)
  obtain ⟨z, hz⟩ := G.exists_character_order hsplit (n + 1)
  obtain ⟨y, hy, hmap⟩ := CharacterGenerators.FiniteEtale.generator_lift n
    (FiniteEtale.FiniteCommGroupScheme.characterMap (G.inclusion n))
    (FiniteEtale.FiniteCommGroupScheme.characterMap_surjective (G.inclusion n)) z hz
    (by rw [(G.level (n + 1)).characterGroup_card, G.rank, Nat.mul_one])
    (by rw [(G.level n).characterGroup_card, G.rank, Nat.mul_one]) x.val x.property
  exact ⟨⟨y, hy⟩, hmap⟩

/-- A compatible system of full-order coordinate characters. -/
def FiniteEtale.PDivisibleGroup.compatibleCharacters (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra) :
    ∀ n, G.CharacterGenerator n
  | 0 => ⟨1, by simp⟩
  | n + 1 => Classical.choose (G.character_generator_lift hsplit n
      (compatibleCharacters G hsplit n))

/-- Restricting the chosen character at the next level gives the preceding character. -/
theorem FiniteEtale.PDivisibleGroup.compatibleCharacters_restriction (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra) (n : ℕ) :
    FiniteEtale.FiniteCommGroupScheme.characterMap (G.inclusion n) (G.compatibleCharacters hsplit (n + 1)).val =
      (G.compatibleCharacters hsplit n).val :=
  Classical.choose_spec (G.character_generator_lift hsplit n (G.compatibleCharacters hsplit n))

/-- Each chosen character generates all characters of its level. -/
theorem FiniteEtale.PDivisibleGroup.compatibleCharacters_generate (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra) (n : ℕ) :
    ∀ x : (G.level n).characterGroup, x ∈ Subgroup.zpowers (G.compatibleCharacters hsplit n).val := by
  have := hsplit n
  have htop : Subgroup.zpowers (G.compatibleCharacters hsplit n).val = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    rw [Nat.card_zpowers, (G.compatibleCharacters hsplit n).property,
      (G.level n).characterGroup_card, G.rank, Nat.mul_one]
  intro x
  rw [htop]
  trivial

end

end OAI.AlgebraicGeometry.GroupSchemes
