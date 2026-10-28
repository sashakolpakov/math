import OAI.AlgebraicGeometry.GroupSchemes.EtaleCyclic

/-! # Etale Generators -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! Compatible choices of full-order points in a split height-one tower. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {p : ℕ} [Fact p.Prime]

/-- Multiplication-down on rational points. -/
def FiniteEtale.PDivisibleGroup.downOnPoints (G : FiniteEtale.PDivisibleGroup k p 1) (n : ℕ) :
    (G.level (n + 1)).rationalPoints →* (G.level n).rationalPoints :=
  ((FiniteEtale.FiniteCommGroupScheme.mapPoints (G.multiplyDown n)).app (CommAlgCat.of k k)).hom

/-- Multiplication-down is surjective in the split tower. -/
theorem FiniteEtale.PDivisibleGroup.downOnPoints_surjective (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ) :
    Function.Surjective (G.downOnPoints n) := by
  have := hsplit n
  have := hsplit (n + 1)
  have := G.rationalPoints_cyclic hsplit (n + 1)
  have hker : (G.downOnPoints n).ker =
      (powMonoidHom p : (G.level (n + 1)).rationalPoints →* (G.level (n + 1)).rationalPoints).ker := by
    ext x
    exact G.multiplyDown_kernel n (CommAlgCat.of k k) x
  apply (G.downOnPoints n).surjective_of_card_ker_le_div
  rw [hker, IsCyclic.card_powMonoidHom_ker,
    (G.level (n + 1)).rationalPoints_card, (G.level n).rationalPoints_card,
    G.rank, G.rank, Nat.mul_one, Nat.mul_one, pow_succ]
  rw [Nat.gcd_eq_right (dvd_mul_left p (p ^ n)), Nat.mul_div_cancel_left _
    (pow_pos (Fact.out : p.Prime).pos n)]

/-- A point of the full prescribed order. -/
def FiniteEtale.PDivisibleGroup.PointGenerator (G : FiniteEtale.PDivisibleGroup k p 1) (n : ℕ) :=
  { x : (G.level n).rationalPoints // orderOf x = p ^ n }

/-- Every generator lifts under multiplication-down to a generator of the next level. -/
theorem FiniteEtale.PDivisibleGroup.generator_lift (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra)
    (n : ℕ) (x : G.PointGenerator n) :
    ∃ y : G.PointGenerator (n + 1), G.downOnPoints n y.val = x.val := by
  cases n with
  | zero =>
    obtain ⟨y, hy⟩ := G.exists_point_order hsplit 1
    refine ⟨⟨y, hy⟩, ?_⟩
    have hx : x.val = 1 := by
      simpa only [pow_zero, pow_one] using G.annihilated k 0 (CommAlgCat.of k k) x.val
    have hd : G.downOnPoints 0 y = 1 := by
      simpa only [pow_zero, pow_one] using
        G.annihilated k 0 (CommAlgCat.of k k) (G.downOnPoints 0 y)
    exact hd.trans hx.symm
  | succ n =>
    obtain ⟨y, hy⟩ := G.downOnPoints_surjective hsplit (n + 1) x.val
    refine ⟨⟨y, orderOf_eq_prime_pow ?_
      (G.annihilated k (n + 1 + 1) (CommAlgCat.of k k) y)⟩, hy⟩
    intro hbad
    have hxpow : x.val ^ (p ^ n) = 1 := by
      apply (cancel_mono (G.inclusion (n + 1))).mp
      rw [MonObj.pow_comp, ← hy, MonObj.one_comp]
      change ((y ≫ G.multiplyDown (n + 1)) ≫ G.inclusion (n + 1)) ^ (p ^ n) = 1
      rw [Category.assoc, G.multiplyDown_points, ← pow_mul, ← pow_succ']
      exact hbad
    exact pow_ne_one_of_lt_orderOf (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
      (by rw [x.property]; exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.lt_succ_self n)) hxpow

/-- A recursive compatible system of full-order generators. -/
def FiniteEtale.PDivisibleGroup.compatibleGenerators (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) : ∀ n, G.PointGenerator n
  | 0 => ⟨1, by simp⟩
  | n + 1 => Classical.choose (G.generator_lift hsplit n (compatibleGenerators G hsplit n))

/-- The chosen generators lift each other under multiplication-down. -/
theorem FiniteEtale.PDivisibleGroup.compatibleGenerators_down (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ) :
    G.downOnPoints n (G.compatibleGenerators hsplit (n + 1)).val =
      (G.compatibleGenerators hsplit n).val :=
  Classical.choose_spec (G.generator_lift hsplit n (G.compatibleGenerators hsplit n))

/-- The original inclusions send each generator to the pth power of the next one. -/
theorem FiniteEtale.PDivisibleGroup.compatibleGenerators_inclusion (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ) :
    (G.compatibleGenerators hsplit n).val ≫ G.inclusion n =
      (G.compatibleGenerators hsplit (n + 1)).val ^ p := by
  have hd : (G.compatibleGenerators hsplit (n + 1)).val ≫ G.multiplyDown n =
      (G.compatibleGenerators hsplit n).val := G.compatibleGenerators_down hsplit n
  rw [← G.multiplyDown_points n (CommAlgCat.of k k), ← Category.assoc, hd]

/-- Each chosen point generates its entire finite point group. -/
theorem FiniteEtale.PDivisibleGroup.compatibleGenerators_generate (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ) :
    ∀ x : (G.level n).rationalPoints, x ∈ Subgroup.zpowers (G.compatibleGenerators hsplit n).val := by
  have := hsplit n
  have htop : Subgroup.zpowers (G.compatibleGenerators hsplit n).val = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    rw [Nat.card_zpowers, (G.compatibleGenerators hsplit n).property,
      (G.level n).rationalPoints_card, G.rank, Nat.mul_one]
  intro x
  rw [htop]
  trivial

/-- Cyclic coordinates chosen compatibly with the geometric transitions. -/
def FiniteEtale.PDivisibleGroup.cyclicPointEquiv (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ) :
    Multiplicative (ZMod (p ^ n)) ≃* (G.level n).rationalPoints :=
  zmodMulEquivOfGenerator (G.compatibleGenerators_generate hsplit n) (by
    have := hsplit n
    rw [(G.level n).rationalPoints_card, G.rank, Nat.mul_one])

/-- The cyclic point coordinates evaluate integer classes by powers of the chosen generator. -/
theorem FiniteEtale.PDivisibleGroup.cyclicPointEquiv_intCast (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ) (z : ℤ) :
    G.cyclicPointEquiv hsplit n (Multiplicative.ofAdd (z : ZMod (p ^ n))) =
      (G.compatibleGenerators hsplit n).val ^ z :=
  zmodMulEquivOfGenerator_apply_ofAdd_intCast _ _ z

/-- The cyclic coordinates respect the original transition inclusions. -/
theorem FiniteEtale.PDivisibleGroup.cyclicPointEquiv_compatibility (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ)
    (a : ZMod (p ^ n)) :
    G.cyclicPointEquiv hsplit n (Multiplicative.ofAdd a) ≫ G.inclusion n =
      G.cyclicPointEquiv hsplit (n + 1) (Multiplicative.ofAdd (FiniteEtale.cyclicInclusion p n a)) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  rw [FiniteEtale.PDivisibleGroup.cyclicPointEquiv_intCast, GrpObj.zpow_comp, G.compatibleGenerators_inclusion,
    FiniteEtale.cyclicInclusion_intCast]
  have hz : p • (z : ZMod (p ^ (n + 1))) = (((p : ℤ) * z : ℤ) : ZMod (p ^ (n + 1))) := by
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  rw [hz, FiniteEtale.PDivisibleGroup.cyclicPointEquiv_intCast, zpow_mul, zpow_natCast]

end

end OAI.AlgebraicGeometry.GroupSchemes
