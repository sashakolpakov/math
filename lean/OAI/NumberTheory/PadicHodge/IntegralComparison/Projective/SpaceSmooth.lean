import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Space Smooth -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SpaceSmooth

noncomputable section

/-! Polynomial projective space is smooth over its original coefficient
ring, as witnessed by its actual polynomial coordinate charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomogeneousLocalization

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def chartEquiv (i : σ) :
    Away (homogeneousSubmodule σ R) (MvPolynomial.X i) ≃ₐ[R] MvPolynomial {j : σ // j ≠ i} R := by
  classical
  exact { OAI.AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R i with commutes' := OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.chartRingEquiv_algebraMap i }

theorem chart_smooth (i : σ) :
    Algebra.Smooth R (Away (homogeneousSubmodule σ R) (MvPolynomial.X i)) := by
  let : Algebra.Smooth R (MvPolynomial {j : σ // j ≠ i} R) := {}
  exact Algebra.Smooth.of_equiv (chartEquiv (R := R) i).symm

theorem smooth : Smooth (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth) _
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := R) (σ := σ))]
  intro i
  let e := Proj.basicOpenIsoSpec (homogeneousSubmodule σ R) (MvPolynomial.X i)
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) e.inv]
  change Smooth (e.inv ≫ (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι ≫ OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)
  rw [OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ, ← Category.assoc, ← Category.assoc, ← Proj.awayι,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change RingHom.Smooth (algebraMap R (Away (homogeneousSubmodule σ R) (MvPolynomial.X i)))
  exact RingHom.smooth_algebraMap.mpr (chart_smooth i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SpaceSmooth
