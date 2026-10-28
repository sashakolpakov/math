import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicDegreeSequence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ExactSequenceFinrank

/-! # Graded Cyclic Finrank -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicFinrank

noncomputable section

/-! Dimension additivity for a homogeneous cyclic extension. -/

open DirectSum
universe u v w

variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
variable {M : Type w} [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M]
variable (𝒜 : ℤ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule K M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

theorem cyclicDegreeSequence_finrank (P : Submodule A M) (hP : P.IsHomogeneous ℳ)
    {m : M} {e : ℤ} (hm : m ∈ ℳ e) (d : ℤ) [Module.Finite K (ℳ d)] :
    (Module.finrank K (GradedCyclicDegreeSequence.DegreeQuotient ℳ P d) : ℚ) =
      (Module.finrank K (GradedCyclicDegreeSequence.DegreeQuotient ℳ (P ⊔ Submodule.span A {m}) d) : ℚ) +
      (Module.finrank K (GradedCyclicDegreeSequence.DegreeQuotient 𝒜 (GradedCyclicSubmodule.relativeAnnihilator P m) (d - e)) : ℚ) := by
  let f := GradedCyclicDegreeSequence.cyclicDegreeInjection 𝒜 ℳ P hm d
  let g := GradedCyclicDegreeSequence.degreeQuotientMap ℳ (show P ≤ P ⊔ Submodule.span A {m} from le_sup_left) d
  have h := ExactSequenceFinrank.finrank_eq_ranges_of_exact f g (GradedCyclicDegreeSequence.cyclicDegreeSequence_exact 𝒜 ℳ P hP hm d)
  rw [LinearMap.finrank_range_of_inj (GradedCyclicDegreeSequence.cyclicDegreeInjection_injective 𝒜 ℳ P hm d),
    LinearMap.range_eq_top.mpr (GradedCyclicDegreeSequence.degreeQuotientMap_surjective ℳ _ d),
    finrank_top] at h
  exact_mod_cast (h.trans (add_comm _ _))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicFinrank
