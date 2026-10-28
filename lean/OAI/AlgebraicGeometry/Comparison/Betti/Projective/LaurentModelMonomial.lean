import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentSourceFactors
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentBaseScalarNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Monomial

/-! # Laurent Model Monomial -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentModelMonomial.Dolbeault

noncomputable section

/-! The original comparison on its homogeneous Laurent source sends each coefficient to the same analytic monomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

open _root_.MvPolynomial

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveLaurentOriginalComparison_monomial (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (b : (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j d).X q)
    (t : Fin (q + 1) → Fin (n + 1)) (ht : StrictMono t)
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image t))
    (e : SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent t))
    (r : Γ(Spec (CommRingCat.of ℂ), ⊤))
    (hb : LaurentOrderedFactors.Dolbeault.algebraicHomogeneousLaurentFactorProjection (R := ℂ) d q ⟨(fun k => ULift.up (t k)), ht⟩ b =
      AddMonoidAlgebra.single (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv t d e) r) :
    ProjectiveTwist.CechConeEvaluation.Dolbeault.projectiveTwistCechConeValue n j d q ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j d).f q b) t x =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r *
        ∏ i, x.val i ^ (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv t d e).val.val i := by
  let z := (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d).inv.f q b
  let m := CechFrameTransport.Dolbeault.projectiveAlgebraicCechBaseFactor n j d q z t
  have hfactor := (LaurentSourceFactors.Dolbeault.projectiveLaurentToNative_factor n j d q b t ht).trans hb
  have hscalar := LaurentBaseScalarNormalization.Dolbeault.coordinateBaseHomogeneousLaurent_single (R := ℂ)
    (fun k => ULift.up (t k)) d
    ((SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := ℂ) (fun k => ULift.up (t k)) j d).hom m)
    e r hfactor
  have hc := (CechFrameTransport.Dolbeault.projectiveAlgebraicTwistCechLaurentCoordinates_baseFactor n j d q z t).trans hscalar
  exact ProjectiveTwist.Monomial.Dolbeault.projectiveTwistCechConeValue_original_map_monomial n j d q z t x e
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r) hc

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentModelMonomial.Dolbeault
