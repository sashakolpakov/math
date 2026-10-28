import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNonnegativeSyzygy
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCokernelDegree

/-! # Finite Graded Quotient -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGradedQuotient

noncomputable section

/-! The finite graded quotient module and its actual degree pieces. -/

set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] {σ : Type}

def finiteGradedQuotient (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R)
    (P : Submodule (MvPolynomial σ R) D.Carrier) (hP : P.IsHomogeneous D.grading) :
    HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R := by
  letI := GradedModuleMk.GradedModuleQuotient.quotientDecomposition D.grading P hP
  exact { Carrier := D.Carrier ⧸ P, grading := GradedModuleMk.GradedModuleQuotient.grading D.grading P }

theorem finiteGradedQuotient_nonnegative (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R)
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) (P : Submodule (MvPolynomial σ R) D.Carrier)
    (hP : P.IsHomogeneous D.grading) : GradedNonnegativeSyzygy.HasNonnegativeGrading (finiteGradedQuotient D P hP) := by
  intro d hd
  change (D.grading d).map (GradedModuleMk.GradedModuleQuotient.quotientMap (R := R) P) = ⊥
  rw [hD d hd, Submodule.map_bot]

def finiteGradedQuotientDegreeEquiv (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R)
    (P : Submodule (MvPolynomial σ R) D.Carrier) (hP : P.IsHomogeneous D.grading) (d : ℤ) :
    GradedCyclicDegreeSequence.DegreeQuotient D.grading P d ≃ₗ[R] (finiteGradedQuotient D P hP).grading d := by
  let f := GradedModuleMk.GradedModuleQuotient.degreeMap D.grading P d
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y, hy, hxy⟩ := x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  have hk : f.ker = GradedCyclicDegreeSequence.degreeRelations D.grading P d := by
    ext x
    change f x = 0 ↔ x.val ∈ P
    constructor
    · intro hx
      apply (Submodule.Quotient.mk_eq_zero P).mp
      exact congrArg Subtype.val hx
    · intro hx
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero P).mpr hx
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGradedQuotient
