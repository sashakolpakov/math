import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.EndomorphismDivisibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservingUnits

/-! # Unit Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full-level automorphisms are congruent to the identity in the actual endomorphism ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g n : ℕ}

theorem Abelian.Schemes.AbelianScheme.mem_levelUnitSubgroup_iff_congruence
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel n) (v : A.EndRingˣ) :
    v ∈ A.levelUnitSubgroup n ↔ ∃ d : A.EndRing, n • d = v.val - 1 := by
  let φ := A.endRingTorsionAction n (Over.mk (𝟙 (Spec (.of K))))
  have h : φ (v.val - 1) = 0 ↔ φ v.val = 1 := by
    rw [map_sub, map_one, sub_eq_zero]
  exact (A.mem_levelUnitSubgroup_iff n v).trans
    (h.symm.trans (A.fullLevel_endomorphism_divisibility level (v.val - 1)))

theorem Moduli.Isomorphisms.LevelPreservingIso.endRingUnit_congruence {δ : Fin g → ℕ}
    {A : PolarizationData.PolarizedAbelianWithFullLevel g δ n (Spec (.of K))} (e : Moduli.Isomorphisms.LevelPreservingIso A A) :
    ∃ d : A.abelian.EndRing, n • d = e.endRingUnit.val - 1 :=
  (A.abelian.mem_levelUnitSubgroup_iff_congruence A.level e.endRingUnit).mp e.levelUnit.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
