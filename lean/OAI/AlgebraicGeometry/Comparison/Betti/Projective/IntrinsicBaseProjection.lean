import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechFrameTransport
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentComplex

/-! # Intrinsic Base Projection -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntrinsicBaseProjection.Dolbeault

noncomputable section

section

/-! The native algebraic Cech comparison preserves the original base-linear intersection projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open _root_.MvPolynomial Scheme.Modules

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveAlgebraicNativeBaseIso_factor (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (b : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ))).X q)
    (t : Fin (q + 1) → Fin (n + 1)) :
    CechFrameTransport.Dolbeault.projectiveAlgebraicCechBaseFactor n j d q ((LaurentComplex.Dolbeault.projectiveAlgebraicNativeBaseIso n j d).hom.f q b) t =
      Pi.π (fun a : Fin (q + 1) → ULift.{0} (Fin (n + 1)) =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ)) q a)
        (fun k => ULift.up (t k)) b := by
  let M := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d
  let U := SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ) (σ := Fin (n + 1))
  let π := SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1))
  let B := SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π M U
  let E := LaurentComplex.Dolbeault.projectiveAlgebraicCechULiftIso n j d
  let z := (LaurentComplex.Dolbeault.projectiveAlgebraicNativeBaseIso n j d).hom.f q b
  let P := fun a : Fin (q + 1) → ULift.{0} (Fin (n + 1)) =>
    M.val.presheaf.obj (op (∏ᶜ fun k => U (a k)))
  have he := ConcreteCategory.congr_hom
    (AdditiveCechReindex.additiveCechReindexIso_hom_proj M.val.presheaf (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n)
      (Equiv.ulift : ULift.{0} (Fin (n + 1)) ≃ Fin (n + 1)) q (fun k => ULift.up (t k))) z
  have hb := ConcreteCategory.congr_hom (SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso_component π M U q
    (fun k => ULift.up (t k))) b
  have hcancel : E.hom.f q z = B.hom.f q b :=
    Iso.inv_hom_id_apply ((HomologicalComplex.eval AddCommGrpCat (.up ℕ) q).mapIso E) (B.hom.f q b)
  rw [CechFrameTransport.Dolbeault.projectiveAlgebraicCechBaseFactor, SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply]
  exact he.symm.trans ((congrArg (fun v => Pi.π P (fun k => ULift.up (t k)) v) hcancel).trans hb)

end

/-! Ordered algebraic Cech cochains retain their actual components in the native original complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open _root_.MvPolynomial Scheme.Modules

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveOrderedBaseToNative (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    ((SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).mapHomologicalComplex (.up ℕ)).obj
      (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ))) ⟶
      ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d :=
  ((SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).mapHomologicalComplex (.up ℕ)).map
    (SheafCohomology.Projective.OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternating (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ))) ≫
        (LaurentComplex.Dolbeault.projectiveAlgebraicNativeBaseIso n j d).hom

theorem projectiveOrderedBaseToNative_factor (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (b : (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ))).X q)
    (t : Fin (q + 1) → Fin (n + 1)) (ht : StrictMono t) :
    CechFrameTransport.Dolbeault.projectiveAlgebraicCechBaseFactor n j d q ((projectiveOrderedBaseToNative n j d).f q b) t =
      Pi.π (fun a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{0} (Fin (n + 1))) q =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ)) q a.val)
        ⟨(fun k => ULift.up (t k)), ht⟩ b := by
  let π := SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1))
  let M := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d
  let U := SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ) (σ := Fin (n + 1))
  have h := projectiveAlgebraicNativeBaseIso_factor n j d q ((SheafCohomology.Projective.OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternating π M U).f q b) t
  have h' := ConcreteCategory.congr_hom (SheafCohomology.Projective.OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF_comp_π_of_strictMono
    π M U q (fun k => ULift.up (t k)) ht) b
  exact h.trans h'

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntrinsicBaseProjection.Dolbeault
