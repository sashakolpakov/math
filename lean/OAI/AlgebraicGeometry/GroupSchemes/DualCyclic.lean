import OAI.AlgebraicGeometry.GroupSchemes.MultiplicativeLevels
import OAI.AlgebraicGeometry.GroupSchemes.PowerCoordinates
import OAI.AlgebraicGeometry.GroupSchemes.NontrivialMultiplication
import OAI.AlgebraicGeometry.GroupSchemes.EtaleCyclic

/-! # Dual Cyclic -/

namespace OAI.AlgebraicGeometry.GroupSchemes.DualCyclic

noncomputable section

/-! The split Cartier-dual levels in height one have cyclic rational-point groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.GroupSchemes.PowerCoordinates.FiniteEtale

namespace FiniteEtale

universe u
variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A]
  [Coalgebra.IsCocomm k A] [Module.Finite k A]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

local instance : CommRing (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convCommRing
local instance : Algebra k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convAlgebra

/-- If a split dual's rational points are killed by p^n, so is multiplication on the original. -/
theorem constant_of_dual_points [Algebra.IsFiniteSplit k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A)] (n : ℕ)
    (hpoints : ∀ y : (FiniteEtale.FiniteCommGroupScheme.dualOfHopf (k := k) A).rationalPoints,
      y ^ (p ^ n) = 1) (x : A) :
    PowerCoordinates.FiniteEtale.powerMap k A (p ^ n) x = algebraMap k A (Coalgebra.counit (R := k) x) := by
  have hpow : ∀ f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A →ₐ[k] k, (toConv f) ^ (p ^ n) = 1 := by
    intro f
    let e := @Spec.mapMulEquiv k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) k _ _ _ inferInstance _
    apply e.injective
    exact (map_pow e (toConv f) (p ^ n)).trans ((hpoints (e (toConv f))).trans e.map_one.symm)
  exact PowerCoordinates.FiniteEtale.powerMap_constant_of_dual k A p n
    (fun f => PowerCoordinates.FiniteEtale.powerMap_constant_of_points k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) (p ^ n) hpow f) x

end FiniteEtale

namespace FiniteEtale.PDivisibleGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- The dual point group contains a point of order p^n when all dual levels split. -/
theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.PDivisibleGroup.exists_dual_point_order (G : GroupSchemes.FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra) (n : ℕ) :
    ∃ x : (G.level n).cartierDual.rationalPoints, orderOf x = p ^ n := by
  cases n with
  | zero => exact ⟨1, by simp⟩
  | succ n =>
    have := hsplit (n + 1)
    have hcard : Nat.card (G.level (n + 1)).cartierDual.rationalPoints = p ^ (n + 1) := by
      rw [(G.level (n + 1)).cartierDual.rationalPoints_card,
        (G.level (n + 1)).cartierDual_rank, G.rank, Nat.mul_one]
    have hex : ∃ x : (G.level (n + 1)).cartierDual.rationalPoints, x ^ (p ^ n) ≠ 1 := by
      by_contra h
      push Not at h
      have hzero := @constant_of_dual_points
        k (G.level (n + 1)).algebra _ _ (G.level (n + 1)).coordinateHopf
        (G.level (n + 1)).coordinateHopf_cocomm (G.level (n + 1)).finite
        p _ _ _ (hsplit (n + 1)) n h
      apply G.identity_power_ne_one n
      have halg : (G.level (n + 1)).coordinatePower (p ^ n) =
          (G.level (n + 1)).coordinateIdentity (G.level (n + 1)).algebra := by
        ext x
        exact hzero x
      have hp := ((G.level (n + 1)).coordinatePoints_pow_eq_one_iff
        (G.level (n + 1)).algebra (AlgHom.id k (G.level (n + 1)).algebra) (p ^ n)).mpr
          (by simpa only [AlgHom.id_comp] using halg)
      have hid : (G.level (n + 1)).coordinatePoints (G.level (n + 1)).algebra
          (toConv (AlgHom.id k (G.level (n + 1)).algebra)) = (𝟙 (G.level (n + 1)).scheme) := by
        rw [FiniteEtale.FiniteCommGroupScheme.coordinatePoints_apply]
        exact (algSpec (CommRingCat.of k)).map_id _
      exact (congrArg (fun z => z ^ (p ^ n)) hid).symm.trans hp
    obtain ⟨x, hx⟩ := hex
    refine ⟨x, orderOf_eq_prime_pow hx ?_⟩
    simpa only [hcard] using (pow_card_eq_one' (x := x))

/-- Every split Cartier-dual level is cyclic in height one. -/
theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.PDivisibleGroup.dual_rationalPoints_cyclic (G : GroupSchemes.FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra) (n : ℕ) :
    IsCyclic (G.level n).cartierDual.rationalPoints := by
  have := hsplit n
  obtain ⟨x, hx⟩ := G.exists_dual_point_order hsplit n
  apply isCyclic_of_orderOf_eq_card x
  rw [hx, (G.level n).cartierDual.rationalPoints_card, (G.level n).cartierDual_rank,
    G.rank, Nat.mul_one]

end FiniteEtale.PDivisibleGroup

end

end OAI.AlgebraicGeometry.GroupSchemes.DualCyclic
