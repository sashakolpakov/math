import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.RingTheory.Derivation.Basic

/-! # Map Chain Rule -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.MapChainRule.PDMapChainRule

noncomputable section

/-! # The PD chain rule after a divided-power algebra map -/

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (I : Ideal A) (J : Ideal B)
  (δ : DividedPowers I) (ε : DividedPowers J) (q : A →ₐ[R] B)
  (hq : DividedPowers.IsDPMorphism δ ε q.toRingHom)
  (D : Derivation R B B)
  (hD : ∀ n b, b ∈ J → D (ε.dpow (n + 1) b) = ε.dpow n b * D b)

include hq hD in
theorem rule (n : ℕ) (a : A) (ha : a ∈ I) :
    D (q (δ.dpow (n + 1) a)) = q (δ.dpow n a) * D (q a) := by
  have hqa : q a ∈ J := hq.ideal_comp (Ideal.mem_map_of_mem q.toRingHom ha)
  exact (congrArg D (hq.map_dpow ha)).trans ((hD n _ hqa).trans
    (congrArg (fun b => b * D (q a)) (hq.map_dpow (n := n) ha).symm))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.MapChainRule.PDMapChainRule
