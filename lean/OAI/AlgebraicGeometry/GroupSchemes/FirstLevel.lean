import OAI.AlgebraicGeometry.GroupSchemes.PrimeDichotomy
import OAI.AlgebraicGeometry.GroupSchemes.DualPoints

/-! # First Level -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! The height-one first level is split étale or has split étale Cartier dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- In the connected case, the first-level Cartier dual is split étale. -/
theorem FiniteEtale.PDivisibleGroup.first_dual_split_of_local (G : FiniteEtale.PDivisibleGroup k p 1)
    (hfirst : IsLocalRing (G.level 1).algebra) :
    Algebra.IsFiniteSplit k (G.level 1).cartierDual.algebra := by
  have hdim : Module.finrank k (G.level 1).algebra = p := by
    simpa only [Nat.mul_one, pow_one] using G.rank 1
  have hdimD : Module.finrank k (G.level 1).cartierDual.algebra = p :=
    (G.level 1).cartierDual_rank.trans hdim
  have hpow : ∀ x : FiniteEtale.affine k (CommAlgCat.of k k) ⟶ (G.level 1).cartierDual.scheme,
      x ^ p = 1 := by
    intro x
    exact @DualPoints.FiniteEtale.dualOfHopf_points_pow k (G.level 1).algebra
      _ _ (G.level 1).coordinateHopf (G.level 1).coordinateHopf_cocomm (G.level 1).finite
      p _ _ hfirst hdim x
  exact ((G.level 1).cartierDual.local_or_split p hdimD hpow).resolve_left
    (G.dual_not_local_of_first_local hfirst)

/-- The actual first level in height one is étale or of multiplicative type. -/
theorem FiniteEtale.PDivisibleGroup.first_split_or_dual_split (G : FiniteEtale.PDivisibleGroup k p 1) :
    Algebra.IsFiniteSplit k (G.level 1).algebra ∨
      Algebra.IsFiniteSplit k (G.level 1).cartierDual.algebra := by
  rcases G.first_local_or_split with hlocal | hsplit
  · exact Or.inr (G.first_dual_split_of_local hlocal)
  · exact Or.inl hsplit

end

end OAI.AlgebraicGeometry.GroupSchemes
