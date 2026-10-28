import OAI.AlgebraicGeometry.GroupSchemes.EtaleTower

/-! # Etale Cyclic -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! The finite point groups of a split height-one tower are cyclic of the prescribed orders. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k]

section

/-- Rational points of the actual finite group scheme. -/
abbrev FiniteEtale.FiniteCommGroupScheme.rationalPoints (G : FiniteEtale.FiniteCommGroupScheme k) := FiniteEtale.affine k (CommAlgCat.of k k) ⟶ G.scheme

/-- Rational points in affine coordinates. -/
def FiniteEtale.FiniteCommGroupScheme.rationalPointsEquivAlgHom (G : FiniteEtale.FiniteCommGroupScheme k) :
    G.rationalPoints ≃ (G.algebra →ₐ[k] k) :=
  (G.coordinatePoints (CommAlgCat.of k k)).toEquiv.symm.trans (WithConv.equiv _)

instance FiniteEtale.FiniteCommGroupScheme.rationalPoints_finite (G : FiniteEtale.FiniteCommGroupScheme k) : Finite G.rationalPoints :=
  Finite.of_equiv (G.algebra →ₐ[k] k) G.rationalPointsEquivAlgHom.symm

/-- For a split finite group scheme, rational-point count equals coordinate dimension. -/
theorem FiniteEtale.FiniteCommGroupScheme.rationalPoints_card [IsAlgClosed k] (G : FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.algebra] :
    Nat.card G.rationalPoints = Module.finrank k G.algebra := by
  rw [Nat.card_congr G.rationalPointsEquivAlgHom,
    Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum k G.algebra)]
  have : IsArtinianRing G.algebra := isArtinian_of_tower k inferInstance
  have : Fintype (PrimeSpectrum G.algebra) := Fintype.ofFinite _
  have hdim := (Algebra.FormallyEtale.equivPiOfIsSepClosed k G.algebra).toLinearEquiv.finrank_eq
  simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using hdim.symm

end

variable [IsAlgClosed k] {p : ℕ} [Fact p.Prime]

/-- A split height-one level contains an element of exact order p^n. -/
theorem FiniteEtale.PDivisibleGroup.exists_point_order (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ) :
    ∃ x : (G.level n).rationalPoints, orderOf x = p ^ n := by
  cases n with
  | zero => exact ⟨1, by simp⟩
  | succ n =>
    have := hsplit n
    have := hsplit (n + 1)
    have hlow : Nat.card (G.level n).rationalPoints = p ^ n := by
      rw [(G.level n).rationalPoints_card, G.rank, Nat.mul_one]
    have hhigh : Nat.card (G.level (n + 1)).rationalPoints = p ^ (n + 1) := by
      rw [(G.level (n + 1)).rationalPoints_card, G.rank, Nat.mul_one]
    have hlt : p ^ n < p ^ (n + 1) :=
      Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.lt_succ_self n)
    have hnotsurj : ¬ Function.Surjective
        (fun y : (G.level n).rationalPoints => y ≫ G.inclusion n) := by
      intro h
      have hc := Nat.card_le_card_of_surjective _ h
      rw [hlow, hhigh] at hc
      omega
    simp only [Function.Surjective, not_forall, not_exists] at hnotsurj
    obtain ⟨x, hx⟩ := hnotsurj
    refine ⟨x, orderOf_eq_prime_pow ?_ (G.annihilated k (n + 1) (CommAlgCat.of k k) x)⟩
    intro hp
    obtain ⟨y, hy⟩ := (G.kernel n (CommAlgCat.of k k) x).mpr hp
    exact hx y hy

/-- Each finite point group in the split height-one tower is cyclic. -/
theorem FiniteEtale.PDivisibleGroup.rationalPoints_cyclic (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ) :
    IsCyclic (G.level n).rationalPoints := by
  have := hsplit n
  obtain ⟨x, hx⟩ := G.exists_point_order hsplit n
  apply isCyclic_of_orderOf_eq_card x
  rw [hx, (G.level n).rationalPoints_card, G.rank, Nat.mul_one]

end

end OAI.AlgebraicGeometry.GroupSchemes
