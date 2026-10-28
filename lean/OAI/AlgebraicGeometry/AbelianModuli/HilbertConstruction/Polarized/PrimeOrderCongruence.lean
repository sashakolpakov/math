import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeOrderPrimeCongruence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PrimeDepth
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CoprimeUnitCongruence

/-! # Prime Order Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! At every level at least three, one prime depending only on the level divides each prime-order polarized automorphism difference to every power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.primeOrder_difference_allPowers (hN : 3 ≤ N) :
    ∃ q : ℕ, q.Prime ∧ ∀ (e : Moduli.Isomorphisms.LevelPreservingIso A A) (p : ℕ), p.Prime →
      e.endRingUnit.val ^ p = 1 → ∀ k : ℕ, ∃ d : A.abelian.EndRing,
        (q ^ k) • d = e.endRingUnit.val - 1 := by
  obtain ⟨q, r, hq, hr, hsize, hd⟩ := Level.PrimeDepth.level_exists_prime_depth N hN
  refine ⟨q, hq, fun e p hp he k => ?_⟩
  have : IsAddTorsionFree A.abelian.EndRing := Polarized.HomTorsionFree.polarized_addHom_isAddTorsionFree A A.abelian
  obtain ⟨x, hx⟩ := e.endRingUnit_congruence
  have hcong : ∃ y : A.abelian.EndRing, (q ^ r) • y = e.endRingUnit.val - 1 := by
    refine ⟨(N / q ^ r) • x, ?_⟩
    rw [← mul_smul, Nat.mul_div_cancel' hd]
    exact hx
  exact PrimeOrderPrimeCongruence.primeOrder_primeCongruence_allPowers e.endRingUnit.val p q r hp hq hr hsize he hcong k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
