import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.DifferenceDivisibilityBound
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-! # Prime Divisible Difference Component -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A polarized automorphism difference divisible by every power of an integer at least two is constant on each integral closed subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
variable {Y : Scheme.{u}} [IsIntegral Y] (i : Y ⟶ A.abelian.scheme.left)
variable [IsClosedImmersion i] [Flat (i ≫ A.abelian.scheme.hom)]
variable [LocallyOfFinitePresentation (i ≫ A.abelian.scheme.hom)]

include E

theorem Moduli.Isomorphisms.LevelPreservingIso.difference_constant_of_allPowers (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (q : ℕ) (hq : 2 ≤ q)
    (hdiv : ∀ k : ℕ, ∃ d : A.abelian.EndRing, (q ^ k) • d = e.endRingUnit.val - 1) :
    ∃ a : Spec (.of K) ⟶ A.abelian.scheme.left,
      (i ≫ A.abelian.scheme.hom) ≫ a = i ≫ (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left := by
  by_contra hf
  let B := Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (i ≫ A.abelian.scheme.hom)).obj
    ((E.power.pullback i).tensorPower 4).sheaf)
  obtain ⟨d, hd⟩ := hdiv B
  have hb : (q ^ B) * (q ^ B) + 1 ≤ B := e.differenceDivisibility_degree_bound A E i hf (q ^ B) d hd
  have hpow : B < q ^ B := (Nat.lt_two_pow_self (n := B)).trans_le (pow_le_pow_left' hq B)
  have hsq : q ^ B ≤ (q ^ B) * (q ^ B) := Nat.le_mul_self _
  exact (not_lt_of_ge hb) ((hpow.trans_le hsq).trans (Nat.lt_succ_self _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
