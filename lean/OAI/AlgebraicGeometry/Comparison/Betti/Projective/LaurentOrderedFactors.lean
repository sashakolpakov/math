import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights

/-! # Laurent Ordered Factors -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentOrderedFactors.Dolbeault

noncomputable section

/-! The existing ordered Laurent complex isomorphism preserves the actual factor coefficient maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Scheme.Modules

universe u

variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def algebraicTwistOrderedLaurentIso (j : σ) (d : ℤ) :
    SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R)) ≅
      SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d :=
  SheafCohomology.Projective.TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := R) j d ≪≫
    SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := R) j d

def algebraicTwistOrderedFactorProjection (j : σ) (d : ℤ) (q : ℕ)
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) q) :
    (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R))).X q ⟶
      SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R)) q a.val :=
  Pi.π _ a

def algebraicHomogeneousLaurentFactorProjection (d : ℤ) (q : ℕ)
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) q) :
    SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d q ⟶
      ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤)
        (AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤)
          {e : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d // e.IsAllowedOn (fun k => (a.val k).down)}) :=
  Pi.π _ a

theorem algebraicTwistOrderedLaurentIso_factor (j : σ) (d : ℤ) (q : ℕ)
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) q)
    (b : (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R))).X q) :
    SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a.val d
      ((SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j d).hom
        (algebraicTwistOrderedFactorProjection (R := R) j d q a b)) =
      algebraicHomogeneousLaurentFactorProjection (R := R) d q a
        ((algebraicTwistOrderedLaurentIso (R := R) j d).hom.f q b) := by
  have h₁ := ConcreteCategory.congr_hom
    (SheafCohomology.Projective.TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit_hom_comp_π (R := R) j d q a) b
  have h₂ := ConcreteCategory.congr_hom
    (SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso_hom_comp_π (R := R) d q a)
    ((SheafCohomology.Projective.TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit (R := R) j d q).hom b)
  exact (congrArg (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a.val d) h₁).symm.trans h₂.symm

theorem algebraicTwistOrderedLaurentIso_inv_factor (j : σ) (d : ℤ) (q : ℕ)
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) q)
    (b : (SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).X q) :
    SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a.val d
      ((SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j d).hom
        (algebraicTwistOrderedFactorProjection (R := R) j d q a
          ((algebraicTwistOrderedLaurentIso (R := R) j d).inv.f q b))) =
      algebraicHomogeneousLaurentFactorProjection (R := R) d q a b := by
  have h := algebraicTwistOrderedLaurentIso_factor (R := R) j d q a
    ((algebraicTwistOrderedLaurentIso (R := R) j d).inv.f q b)
  have hc := Iso.inv_hom_id_apply
    ((HomologicalComplex.eval (ModuleCat Γ(Spec (CommRingCat.of R), ⊤)) (.up ℕ) q).mapIso
      (algebraicTwistOrderedLaurentIso (R := R) j d)) b
  exact h.trans (congrArg (algebraicHomogeneousLaurentFactorProjection (R := R) d q a) hc)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentOrderedFactors.Dolbeault
