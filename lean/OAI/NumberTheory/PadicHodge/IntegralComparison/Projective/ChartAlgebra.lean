import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SpaceSmooth
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ToSpecZero
import OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms

/-! # Chart Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ChartAlgebra

noncomputable section

/-! Polynomial coordinates on an actual projective chart respect the
original structural coefficient map used by algebraic differential forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev algebra (U : (Proj (homogeneousSubmodule σ R)).Opens) :
    Algebra R Γ(Proj (homogeneousSubmodule σ R), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))) U

def equiv (i : σ) :
    letI := algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≃ₐ[R]
      MvPolynomial {j : σ // j ≠ i} R := by
  classical
  letI := algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  let e := (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (MvPolynomial.X i)
    (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).commRingCatIsoToRingEquiv
  refine { __ := e.symm.trans (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R i), commutes' := ?_ }
  intro r
  have hs := ConcreteCategory.congr_hom
    (AlgebraicGeometry.SheafCohomology.Projective.ToSpecZero.Proj_structure_section_square (homogeneousSubmodule σ R)
      (algebraMap R (homogeneousSubmodule σ R 0)) (MvPolynomial.X i)
      (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos) r
  change e.symm (algebraMap R Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) r) =
    algebraMap R (HomogeneousLocalization.Away (homogeneousSubmodule σ R) (MvPolynomial.X i)) r at hs
  exact (congrArg (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R i) hs).trans (AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.chartRingEquiv_algebraMap i r)

omit [Finite σ] in
theorem equiv_coordinate (i : σ) (j : {j : σ // j ≠ i}) :
    letI := algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    equiv (R := R) i (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) = MvPolynomial.X j := by
  classical
  let := algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_of_ne i j j.property]
  change AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R i
      ((Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (MvPolynomial.X i)
        (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).commRingCatIsoToRingEquiv.symm
          ((Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (MvPolynomial.X i)
            (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).commRingCatIsoToRingEquiv
              (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.awayVar R i j))) = _
  rw [RingEquiv.symm_apply_apply, AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv_apply_awayVar]

omit [Finite σ] in
theorem equiv_symm_variable (i : σ) (j : {j : σ // j ≠ i}) :
    letI := algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (equiv (R := R) i).symm (MvPolynomial.X j) = AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j := by
  let := algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  apply (equiv (R := R) i).injective
  rw [AlgEquiv.apply_symm_apply, equiv_coordinate]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ChartAlgebra
