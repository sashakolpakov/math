import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentDifferential
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechHigher
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CycleHomologyDesc

/-! # Negative Laurent Homology -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology

noncomputable section

open _root_.MvPolynomial

/-! Full-negative Laurent coefficients descend to positive cohomology. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.CycleHomologyDesc
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateFullNegativeCycleProjection_boundary (j : σ) (d : ℤ) (n : ℕ) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).toCycles n (n + 1) ≫
      ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).iCycles (n + 1) ≫
        ModuleCat.ofHom (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection (R := R) d (n + 1))) = 0 := by
  rw [← Category.assoc, HomologicalComplex.toCycles_i,
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact NegativeLaurentDifferential.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection_boundary (R := R) d n s

def coordinateFullNegativeHomologyProjection (j : σ) (d : ℤ) (n : ℕ) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology (n + 1) ⟶
      ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤)
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u, u} (R := R) (σ := σ) d (n + 1)) :=
  CycleHomologyDesc.positiveHomologyDesc (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d) n
    ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).iCycles (n + 1) ≫
      ModuleCat.ofHom (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection (R := R) d (n + 1)))
    (coordinateFullNegativeCycleProjection_boundary (R := R) j d n)

theorem coordinateFullNegativeHomologyProjection_homologyπ (j : σ) (d : ℤ) (n : ℕ) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homologyπ (n + 1) ≫
      coordinateFullNegativeHomologyProjection (R := R) j d n =
        (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).iCycles (n + 1) ≫
          ModuleCat.ofHom (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection (R := R) d (n + 1)) :=
  CycleHomologyDesc.positiveHomologyDesc_homologyπ _ _ _ _

variable [Fintype σ]

theorem coordinateFullNegativeCyclesToHomology_projection (j : σ) (d : ℤ) (n : ℕ) :
    TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToHomology (R := R) j d (n + 1) ≫
      coordinateFullNegativeHomologyProjection (R := R) j d n =
        ModuleCat.ofHom (R := Γ(Spec (CommRingCat.of R), ⊤))
          (X := ↥(LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles.{u, u}
            (R := R) (σ := σ) d (n + 1)))
          (Y := LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u, u}
            (R := R) (σ := σ) d (n + 1))
          (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles.{u, u}
            (R := R) (σ := σ) d (n + 1)).subtype := by
  rw [TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToHomology, Category.assoc,
    coordinateFullNegativeHomologyProjection_homologyπ, ← Category.assoc,
    TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToCycles_i]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact NegativeLaurentDifferential.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection_assembly (R := R) d (n + 1) s.val

theorem coordinateHomogeneousLaurentFullNegativeCyclesToHomology_injective
    (j : σ) (d : ℤ) (n : ℕ) :
    Function.Injective
      (TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToHomology (R := R) j d (n + 1)).hom := by
  intro x y h
  have hp := congrArg (fun z => (coordinateFullNegativeHomologyProjection (R := R) j d n).hom z) h
  have he := coordinateFullNegativeCyclesToHomology_projection (R := R) j d n
  have hx := ConcreteCategory.congr_hom he x
  have hy := ConcreteCategory.congr_hom he y
  exact Subtype.ext (hx.symm.trans (hp.trans hy))

def coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles
    (j : σ) (d : ℤ) (n : ℕ) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology (n + 1) ≃ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)]
        LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles.{u, u} (R := R) (σ := σ) d (n + 1) :=
  (LinearEquiv.ofBijective
    (TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToHomology (R := R) j d (n + 1)).hom
    ⟨coordinateHomogeneousLaurentFullNegativeCyclesToHomology_injective (R := R) j d n,
      TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToHomology_surjective (R := R) j d n⟩).symm

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology
