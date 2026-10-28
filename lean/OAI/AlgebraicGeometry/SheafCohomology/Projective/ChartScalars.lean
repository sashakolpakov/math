import OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections

/-! # Chart Scalars -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartScalars.Dimension

noncomputable section

/-! The dehomogenized chart presentation respects the actual base-scheme scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [Fintype σ] in
theorem coordinateChartCoefficientRingHom_baseScalar {m : ℕ}
    (a : Fin (m + 1) → ULift.{u} σ) (r : Γ(Spec (.of R), ⊤)) :
    PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom (R := R) a
      (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenScalarMap (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a 0).down) r) =
    algebraMap Γ(Spec (.of R), ⊤)
      (AddMonoidAlgebra Γ(Spec (.of R), ⊤)
        (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down)))) r := by
  unfold PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom
  rw [RingHom.comp_apply, ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenScalarMap_eq]
  change StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op
        ((Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op
          ((MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop r))) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv_baseScalar a r

theorem projectiveChartPolynomialMap_C (j : σ) (r : Γ(Spec (.of R), ⊤)) :
    ChartPolynomialMap.Dimension.projectiveChartPolynomialMap (R := R) j (C r) =
      ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenScalarMap (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) r := by
  apply (ChartPolynomialMap.Dimension.singleProjectiveChartCoefficientEquiv (R := R) j).injective
  change (ChartPolynomialMap.Dimension.singleProjectiveChartCoefficientEquiv (R := R) j)
      ((ChartPolynomialMap.Dimension.singleProjectiveChartCoefficientEquiv (R := R) j).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  change PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤) (fun _ : Fin 1 => j) (monomial 0 r) = _
  rw [PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial, map_zero]
  exact (coordinateChartCoefficientRingHom_baseScalar (ChartPolynomialMap.Dimension.singleProjectiveChartTuple j) r).symm

def projectiveChartPolynomialAlgHom (j : σ) :
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    MvPolynomial σ Γ(Spec (.of R), ⊤) →ₐ[Γ(Spec (.of R), ⊤)]
      Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) :=
  letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
  { ChartPolynomialMap.Dimension.projectiveChartPolynomialMap j with commutes' := projectiveChartPolynomialMap_C j }

def closedProjectiveChartPolynomialAlgHom {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) :
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    MvPolynomial σ Γ(Spec (.of R), ⊤) →ₐ[Γ(Spec (.of R), ⊤)] Γ(X, f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j) :=
  letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsPullbackAlgHom f MvPolynomialClosure.MvPolynomial.homogeneousProjπ (MvPolynomialClosure.MvPolynomial.coordinateOpen j)).comp
    (projectiveChartPolynomialAlgHom j)

theorem closedProjectiveChartPolynomialAlgHom_surjective {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ) :
    Function.Surjective (closedProjectiveChartPolynomialAlgHom f j) :=
  (f.app_surjective (MvPolynomialClosure.MvPolynomial.coordinateOpen j) (MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen j)).comp
    (ChartPolynomialMap.Dimension.projectiveChartPolynomialMap_surjective j)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartScalars.Dimension
