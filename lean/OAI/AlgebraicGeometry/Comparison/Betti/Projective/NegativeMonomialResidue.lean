import OAI.AlgebraicGeometry.Comparison.Betti.Projective.TopResidueValues
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentModelMonomial
import OAI.AlgebraicGeometry.Comparison.Betti.NegativeAnalyticMonomial

/-! # Negative Monomial Residue -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeMonomialResidue.Dolbeault

noncomputable section

/-! The actual top residue of an original negative Laurent generator is its normalized analytic coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

open _root_.MvPolynomial Scheme.Modules

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

def projectiveOrderedTopTuple (n : ℕ) : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{0} (Fin (n + 1))) n :=
  ⟨ULift.up, strictMono_id⟩

def fullNegativeTopAllowedWeight (n k : ℕ) (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k) :
    {v : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent (Fin (n + 1)) (-(k : ℤ)) //
      v.IsAllowedOn (id : Fin (n + 1) → Fin (n + 1))} :=
  ⟨e.val, fun i _ => ⟨i, rfl⟩⟩

def fullNegativeTopLocalExponent (n k : ℕ) (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k) :
    SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (id : Fin (n + 1) → Fin (n + 1))) :=
  (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv id (-(k : ℤ))).symm (fullNegativeTopAllowedWeight n k e)

theorem projectiveLaurentOriginalComparison_top_negative_monomial (n k : ℕ) (j : Fin (n + 1))
    (b : (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j (-(k : ℤ))).X n)
    (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k) (r : Γ(Spec (CommRingCat.of ℂ), ⊤))
    (hb : LaurentOrderedFactors.Dolbeault.algebraicHomogeneousLaurentFactorProjection (R := ℂ) (-(k : ℤ)) n (projectiveOrderedTopTuple n) b =
      AddMonoidAlgebra.single (fullNegativeTopAllowedWeight n k e) r) :
    ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue n j (-(k : ℤ))
      ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j (-(k : ℤ))).f n b) =
        NegativeAnalyticMonomial.Dolbeault.negativeAnalyticMonomial (n + 1) k e ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r) := by
  apply TopResidueValues.Dolbeault.projectiveTwistTopResidue_of_cone_values
  intro x
  let l := fullNegativeTopLocalExponent n k e
  have hl : SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (id : Fin (n + 1) → Fin (n + 1)) (-(k : ℤ)) l =
      fullNegativeTopAllowedWeight n k e :=
    (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv id (-(k : ℤ))).apply_symm_apply _
  have hb' := hb.trans (congrArg (fun v => AddMonoidAlgebra.single v r) hl.symm)
  have h := LaurentModelMonomial.Dolbeault.projectiveLaurentOriginalComparison_monomial n j (-(k : ℤ)) n b id strictMono_id x l r hb'
  have hp := congrArg (fun v : {v : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent (Fin (n + 1)) (-(k : ℤ)) //
      v.IsAllowedOn (id : Fin (n + 1) → Fin (n + 1))} => ∏ i, x.val i ^ v.val.val i) hl
  exact h.trans ((congrArg ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r * ·) hp).trans
    (NegativeAnalyticMonomial.Dolbeault.negativeAnalyticMonomial_inverse_apply (n + 1) k e ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r) x.val).symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeMonomialResidue.Dolbeault
