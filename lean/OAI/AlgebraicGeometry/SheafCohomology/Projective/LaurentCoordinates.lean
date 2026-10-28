import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSections

/-! # Laurent Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCoordinates

noncomputable section

open _root_.MvPolynomial

/-! Direct Laurent coordinates are the actual restricted section written in its chart frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev HomogeneousLaurentZeroFactor (d : ℤ)
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0) :=
  AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤)
    {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d // e.IsAllowedOn (fun k => (a.val k).down)}

def homogeneousLaurentZeroComponent (d : ℤ) (z : LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d)
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0) : HomogeneousLaurentZeroFactor (R := R) d a :=
  (Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0 =>
    ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤) (HomogeneousLaurentZeroFactor (R := R) d b)) a) z.val

omit [Fintype σ] in
theorem directCoordinateTwistGlobalSectionsLaurentEquiv_component (j : σ) (n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤))
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0) :
    homogeneousLaurentZeroComponent (n : ℤ)
      (PolynomialSections.MvPolynomial.directCoordinateTwistGlobalSectionsLaurentEquiv (R := R) j n x) a =
      StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a.val (n : ℤ)
        ((TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j (n : ℤ)).hom
          ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
            (homOfLE (show (∏ᶜ fun k : Fin 1 => StandardCech.MvPolynomial.coordinateOpenCover (R := R) (a.val k)) ≤ ⊤
              from le_top)).op x)) := by
  let E := TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := R) j (n : ℤ) ≪≫
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := R) j (n : ℤ)
  let q := Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0 =>
    ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤) (HomogeneousLaurentZeroFactor (R := R) (n : ℤ) b)) a
  let p := Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0 =>
    Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0 b.val) a
  let e := TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j (n : ℤ)
  let c := StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a.val (n : ℤ)
  have hp : E.hom.f 0 ≫ q = p ≫ e.hom ≫ c.toModuleIso.hom := by
    dsimp only [E, q, p, e, c]
    simp only [Iso.trans_hom, HomologicalComplex.comp_f,
      TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso_hom_f,
      TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso_hom_f, Category.assoc]
    rw [LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso_hom_comp_π]
    rw [← Category.assoc, TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit_hom_comp_π,
      Category.assoc]
    rfl
  let y := BaseZeroCyclesSections.orderedBaseTopSectionsZeroCyclesAddEquiv (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ)) x
  have hy := BaseZeroCycleCoordinates.orderedBaseTopSectionsZeroCyclesAddEquiv_coordinate
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ)) x a
  unfold homogeneousLaurentZeroComponent
  rw [PolynomialSections.MvPolynomial.directCoordinateTwistGlobalSectionsLaurentEquiv_val]
  exact (ConcreteCategory.congr_hom hp y.val).trans (congrArg (fun z => c (e.hom z)) hy)

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCoordinates
