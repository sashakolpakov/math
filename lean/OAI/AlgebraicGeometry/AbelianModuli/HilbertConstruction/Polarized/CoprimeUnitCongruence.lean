import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoprimeFiniteOrderCongruence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.AutomorphismFiniteOrder
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.UnitCongruence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.HomTorsionFree

/-! # Coprime Unit Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual endomorphism-ring congruence of a polarized automorphism deepens to every level power when a finite order is coprime to that level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem Moduli.Isomorphisms.LevelPreservingIso.endRingUnit_coprime_allPowers (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (n : ℕ) (hn : e.endRingUnit.val ^ n = 1) (hcop : n.Coprime N) (hN : N ≠ 0) (k : ℕ) :
    ∃ d : A.abelian.EndRing, (N ^ k) • d = e.endRingUnit.val - 1 := by
  have : IsAddTorsionFree A.abelian.EndRing := Polarized.HomTorsionFree.polarized_addHom_isAddTorsionFree A A.abelian
  exact CoprimeFiniteOrderCongruence.coprime_finiteOrder_congruence_allPowers e.endRingUnit.val N n hN hcop hn
    e.endRingUnit_congruence k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
