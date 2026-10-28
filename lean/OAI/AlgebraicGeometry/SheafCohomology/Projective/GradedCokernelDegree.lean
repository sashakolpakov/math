import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicDegreeSequence

/-! # Graded Cokernel Degree -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCokernelDegree

noncomputable section

/-! The degreewise cokernel of a homogeneous map is the degree quotient by its full range. -/

open DirectSum OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness.GradedModules
universe u v w t
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
variable (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
variable [Decomposition ℳ] [Decomposition 𝒩]

 theorem homogeneousDegreeMap_range (f : M →ₗ[A] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : ℤ) :
    (HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap ℳ 𝒩 (f.restrictScalars R) hf d).range = GradedCyclicDegreeSequence.degreeRelations 𝒩 f.range d := by
  apply le_antisymm
  · rintro n ⟨m, rfl⟩
    exact ⟨m.val, rfl⟩
  · intro n hn
    obtain ⟨m, hm⟩ := hn
    exact ⟨decompose ℳ m d, Subtype.ext
      (HilbertScheme.Presentations.Graded.Exactness.GradedModules.homogeneous_preimage ℳ 𝒩 (f.restrictScalars R) hf d n.val n.property m hm)⟩

def homogeneousDegreeCokernelEquiv (f : M →ₗ[A] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : ℤ) :
    ((𝒩 d) ⧸ (HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap ℳ 𝒩 (f.restrictScalars R) hf d).range) ≃ₗ[R]
      GradedCyclicDegreeSequence.DegreeQuotient 𝒩 f.range d :=
  Submodule.quotEquivOfEq _ _ (homogeneousDegreeMap_range ℳ 𝒩 f hf d)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCokernelDegree
