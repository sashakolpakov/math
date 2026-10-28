import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedIdealReconstruction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Quotient
import Mathlib.RingTheory.Flat.Basic

/-! # Quotient Flatness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
The actual quotient by a homogeneous ideal is flat exactly when all of its
degree quotients are flat. Applied to reconstructed relations, this proves
flatness directly from the quotient modules parametrized by Grassmannians.
-/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient

universe u v

variable {R : Type u} [CommRing R] {σ : Type v}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) (d : ℕ)

theorem Homogeneous.QuotientFlatness.homogeneousQuotientDegreeMap_ker :
    (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientDegreeMap I d).ker = Homogeneous.IdealIncidence.homogeneousDegreeRelations I d := by
  apply Submodule.ext
  intro p
  change HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientDegreeMap I d p = 0 ↔ p.val ∈ I.toIdeal
  constructor
  · intro h
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h

def Homogeneous.QuotientFlatness.homogeneousDegreeQuotientEquiv :
    (MvPolynomial.homogeneousSubmodule σ R d ⧸ Homogeneous.IdealIncidence.homogeneousDegreeRelations I d) ≃ₗ[R]
      HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I d :=
  (Submodule.quotEquivOfEq _ _ (Homogeneous.QuotientFlatness.homogeneousQuotientDegreeMap_ker I d).symm).trans
    ((HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientDegreeMap I d).quotKerEquivOfSurjective (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientDegreeMap_surjective I d))

theorem Homogeneous.QuotientFlatness.homogeneousQuotient_flat_iff : Module.Flat R (MvPolynomial σ R ⧸ I.toIdeal) ↔
    ∀ d, Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸ Homogeneous.IdealIncidence.homogeneousDegreeRelations I d) := by
  rw [Module.Flat.equiv_iff (DirectSum.decomposeLinearEquiv (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I)),
    Module.Flat.directSum_iff]
  exact forall_congr' (fun d => (Module.Flat.equiv_iff (Homogeneous.QuotientFlatness.homogeneousDegreeQuotientEquiv I d)).symm)

theorem GradedIdealReconstruction.GradedIdealRelations.quotient_flat_iff (D : GradedIdealReconstruction.GradedIdealRelations R σ) :
    Module.Flat R (MvPolynomial σ R ⧸ D.toIdeal) ↔
      ∀ d, Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸ D.piece d) := by
  refine (Homogeneous.QuotientFlatness.homogeneousQuotient_flat_iff D.toHomogeneousIdeal).trans ?_
  exact forall_congr' (fun d => iff_of_eq (congrArg
    (fun N : Submodule R (MvPolynomial.homogeneousSubmodule σ R d) =>
      Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸ N))
    (D.toHomogeneousIdeal_degree d)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
