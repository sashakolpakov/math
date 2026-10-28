import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntrinsicBaseProjection
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentOrderedFactors

/-! # Laurent Source Factors -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentSourceFactors.Dolbeault

noncomputable section

/-! Exact homogeneous Laurent factors after the inverse homotopy equivalence to the original algebraic complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open _root_.MvPolynomial Scheme.Modules

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveLaurentToNative_eq (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d).inv =
      ((SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).mapHomologicalComplex (.up ℕ)).map
        (LaurentOrderedFactors.Dolbeault.algebraicTwistOrderedLaurentIso (R := ℂ) j d).inv ≫ IntrinsicBaseProjection.Dolbeault.projectiveOrderedBaseToNative n j d :=
  Category.assoc _ _ _

theorem projectiveLaurentToNative_factor (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (b : (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j d).X q)
    (t : Fin (q + 1) → Fin (n + 1)) (ht : StrictMono t) :
    SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := ℂ) (fun k => ULift.up (t k)) d
      ((SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := ℂ) (fun k => ULift.up (t k)) j d).hom
        (CechFrameTransport.Dolbeault.projectiveAlgebraicCechBaseFactor n j d q
          ((LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d).inv.f q b) t)) =
      LaurentOrderedFactors.Dolbeault.algebraicHomogeneousLaurentFactorProjection (R := ℂ) d q ⟨(fun k => ULift.up (t k)), ht⟩ b := by
  let a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{0} (Fin (n + 1))) q := ⟨(fun k => ULift.up (t k)), ht⟩
  let c := (LaurentOrderedFactors.Dolbeault.algebraicTwistOrderedLaurentIso (R := ℂ) j d).inv.f q b
  have he : (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d).inv.f q b =
      (IntrinsicBaseProjection.Dolbeault.projectiveOrderedBaseToNative n j d).f q c :=
    congrArg (fun f => f.f q b) (projectiveLaurentToNative_eq n j d)
  have hn := congrArg (fun z => CechFrameTransport.Dolbeault.projectiveAlgebraicCechBaseFactor n j d q z t) he
  have hb := IntrinsicBaseProjection.Dolbeault.projectiveOrderedBaseToNative_factor n j d q c t ht
  have h := congrArg (fun m => SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
    (R := ℂ) a.val d ((SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := ℂ) a.val j d).hom m))
      (hn.trans hb)
  exact h.trans (LaurentOrderedFactors.Dolbeault.algebraicTwistOrderedLaurentIso_inv_factor (R := ℂ) j d q a b)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentSourceFactors.Dolbeault
