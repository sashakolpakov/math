import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedModuleMk
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCokernelDegree

/-! # Graded Quotient Degree Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedQuotientDegreeMap.GradedModuleQuotient

noncomputable section

/-! Surjectivity and kernel of the actual quotient map in each homogeneous degree. -/

open DirectSum
universe u v w
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (ℳ : ℤ → Submodule R M) (P : Submodule A M) (d : ℤ)

theorem degreeMap_surjective : Function.Surjective (GradedModuleMk.GradedModuleQuotient.degreeMap ℳ P d) := by
  intro x
  obtain ⟨y, hy, hxy⟩ := x.property
  exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

theorem degreeMap_kernel : (GradedModuleMk.GradedModuleQuotient.degreeMap ℳ P d).ker = GradedCyclicDegreeSequence.degreeRelations ℳ P d := by
  ext x
  change GradedModuleMk.GradedModuleQuotient.degreeMap ℳ P d x = 0 ↔ x.val ∈ P
  constructor
  · intro hx
    apply (Submodule.Quotient.mk_eq_zero P).mp
    exact congrArg Subtype.val hx
  · intro hx
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero P).mpr hx

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedQuotientDegreeMap.GradedModuleQuotient
