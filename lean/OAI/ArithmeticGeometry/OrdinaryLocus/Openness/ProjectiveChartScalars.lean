import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartPolynomialMap
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections

/-! # Projective Chart Scalars -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartScalars.Construction

noncomputable section

/-! The dehomogenized chart presentation respects the actual base-scheme scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [Fintype σ] in
theorem coordinateChartCoefficientRingHom_baseScalar {m : ℕ}
    (a : Fin (m + 1) → ULift.{u} σ) (r : Γ(Spec (.of R), ⊤)) :
    AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom (R := R) a
      (BaseOpenSections.Construction.baseOpenScalarMap (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a 0).down) r) =
    algebraMap Γ(Spec (.of R), ⊤)
      (AddMonoidAlgebra Γ(Spec (.of R), ⊤)
        (AlgebraicGeometry.SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down)))) r := by
  unfold AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom
  rw [RingHom.comp_apply, BaseOpenSections.Construction.baseOpenScalarMap_eq]
  change AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op
        ((Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op
          ((AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop r))) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv_baseScalar a r

theorem projectiveChartPolynomialMap_C (j : σ) (r : Γ(Spec (.of R), ⊤)) :
    ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap (R := R) j (C r) =
      BaseOpenSections.Construction.baseOpenScalarMap (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) r := by
  apply (ProjectiveChartPolynomialMap.Construction.singleProjectiveChartCoefficientEquiv (R := R) j).injective
  change (ProjectiveChartPolynomialMap.Construction.singleProjectiveChartCoefficientEquiv (R := R) j)
      ((ProjectiveChartPolynomialMap.Construction.singleProjectiveChartCoefficientEquiv (R := R) j).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  change AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤) (fun _ : Fin 1 => j) (monomial 0 r) = _
  rw [AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial, map_zero]
  exact (coordinateChartCoefficientRingHom_baseScalar (ProjectiveChartPolynomialMap.Construction.singleProjectiveChartTuple j) r).symm

def projectiveChartPolynomialAlgHom (j : σ) :
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    MvPolynomial σ Γ(Spec (.of R), ⊤) →ₐ[Γ(Spec (.of R), ⊤)]
      Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) :=
  letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
  { ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap j with commutes' := projectiveChartPolynomialMap_C j }

def closedProjectiveChartPolynomialAlgHom {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) :
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    MvPolynomial σ Γ(Spec (.of R), ⊤) →ₐ[Γ(Spec (.of R), ⊤)] Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) :=
  letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  (BaseOpenSections.Construction.baseOpenSectionsPullbackAlgHom f AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)).comp
    (projectiveChartPolynomialAlgHom j)

theorem closedProjectiveChartPolynomialAlgHom_surjective {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ) :
    Function.Surjective (closedProjectiveChartPolynomialAlgHom f j) :=
  (f.app_surjective (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen j)).comp
    (ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap_surjective j)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartScalars.Construction
