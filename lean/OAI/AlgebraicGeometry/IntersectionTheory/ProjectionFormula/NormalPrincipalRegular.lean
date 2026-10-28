import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalPrincipalAssociated
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeQuotientLocalization
import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # Normal Principal Regular -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalPrincipalRegular

noncomputable section

/-! In a normal Noetherian domain, a function avoiding the height-one
components of a principal divisor acts regularly on its actual quotient. -/

set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

theorem regular (f g : R) (hf : f ≠ 0)
    (havoid : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → f ∈ p → g ∉ p) :
    IsSMulRegular (R ⧸ Ideal.span {f}) g := by
  intro x y hxy
  change g • x = g • y at hxy
  by_contra hn
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hn
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hne
  let := hp.isPrime
  have hheight := NormalPrincipalAssociated.height_one R f hf p hp
  have hfp : f ∈ p := by
    apply hle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact PrimeQuotientLocalization.annihilated R (Ideal.span {f}) f
      (Ideal.subset_span (Set.mem_singleton f)) (x - y)
  apply havoid p hheight hfp
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_sub, hxy, sub_self]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalPrincipalRegular
