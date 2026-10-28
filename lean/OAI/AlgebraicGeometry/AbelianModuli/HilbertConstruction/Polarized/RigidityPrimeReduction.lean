import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.AutomorphismIdentityDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.PrimeOrderCongruence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.OrderPrimeReduction

/-! # Rigidity Prime Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A nontrivial polarized full-level automorphism at level at least three produces a nonzero polarized automorphism difference divisible by every power of one prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem Moduli.Isomorphisms.LevelPreservingIso.exists_nontrivial_primeOrder (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (he : e ≠ Moduli.Isomorphisms.LevelPreservingIso.refl A) :
    ∃ (p : ℕ) (f : Moduli.Isomorphisms.LevelPreservingIso A A), p.Prime ∧ f.endRingUnit.val ^ p = 1 ∧ f.endRingUnit.val ≠ 1 := by
  have := Polarized.AutomorphismFiniteOrder.polarizedAutomorphismUnitSubgroup_finite A
  have hu : e.automorphismUnit ≠ 1 := by
    intro h
    apply he
    exact e.eq_refl_of_endRingUnit_eq_one (congrArg (fun v : A.automorphismUnitSubgroup => v.val.val) h)
  obtain ⟨p, v, hp, hvp, hv1⟩ := Finite.OrderPrimeReduction.finiteOrder_exists_prime_order e.automorphismUnit
    (isOfFinOrder_of_finite e.automorphismUnit) hu
  obtain ⟨f, hf⟩ := Moduli.Isomorphisms.LevelPreservingIso.automorphismUnit_surjective v
  have hfp : f.automorphismUnit ^ p = 1 := (congrArg (fun w : A.automorphismUnitSubgroup => w ^ p) hf).trans hvp
  have hf1 : f.endRingUnit.val ≠ 1 := fun h => hv1 (hf.symm.trans (Subtype.ext (Units.ext h)))
  exact ⟨p, f, hp, congrArg (fun w : A.automorphismUnitSubgroup => w.val.val) hfp, hf1⟩

theorem Moduli.Isomorphisms.LevelPreservingIso.nontrivial_implies_prime_divisible_difference
    (e : Moduli.Isomorphisms.LevelPreservingIso A A) (hN : 3 ≤ N) (he : e ≠ Moduli.Isomorphisms.LevelPreservingIso.refl A) :
    ∃ (q : ℕ) (f : Moduli.Isomorphisms.LevelPreservingIso A A), q.Prime ∧ f.endRingUnit.val - 1 ≠ 0 ∧
      ∀ k : ℕ, ∃ d : A.abelian.EndRing, (q ^ k) • d = f.endRingUnit.val - 1 := by
  obtain ⟨q, hq, hqall⟩ := A.primeOrder_difference_allPowers hN
  obtain ⟨p, f, hp, hfp, hf1⟩ := e.exists_nontrivial_primeOrder A he
  exact ⟨q, f, hq, sub_ne_zero.mpr hf1, hqall f p hp hfp⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
