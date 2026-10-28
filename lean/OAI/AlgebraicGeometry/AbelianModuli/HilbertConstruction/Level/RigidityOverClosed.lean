import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeDivisibleDifferenceVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.RigidityPrimeReduction

/-! # Rigidity Over Closed -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! At level at least three, every actual polarized full-level automorphism over an algebraically closed field is the identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem Moduli.Isomorphisms.LevelPreservingIso.eq_refl_overAlgClosed (e : Moduli.Isomorphisms.LevelPreservingIso A A) (hN : 3 ≤ N) :
    e = Moduli.Isomorphisms.LevelPreservingIso.refl A := by
  by_contra he
  obtain ⟨q, f, hq, hf, hdiv⟩ := e.nontrivial_implies_prime_divisible_difference A hN he
  exact hf (f.difference_zero_of_allPowers A q hq.two_le hdiv)

theorem Level.RigidityOverClosed.polarizedAutomorphisms_subsingleton_overAlgClosed (hN : 3 ≤ N) :
    Subsingleton (Moduli.Isomorphisms.LevelPreservingIso A A) :=
  ⟨fun e d => (e.eq_refl_overAlgClosed A hN).trans (d.eq_refl_overAlgClosed A hN).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
