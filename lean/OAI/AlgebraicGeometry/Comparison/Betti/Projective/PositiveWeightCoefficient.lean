import OAI.AlgebraicGeometry.Comparison.Betti.OrderedEmptySupportValues
import OAI.AlgebraicGeometry.Comparison.Betti.PositiveAnalyticMonomial
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ZeroCoefficientValues
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentModelMonomial
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.WeightInclusionFactors

/-! # Positive Weight Coefficient -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveWeightCoefficient.Dolbeault

noncomputable section

/-! The actual comparison takes each original nonnegative constant-weight zero cycle to its analytic monomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Scheme.Modules

open OAI.AlgebraicGeometry.Comparison.Betti.OrderedEmptySupportValues.Cech

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

def projectiveOrderedZeroTuple (n : ℕ) : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{0} (Fin (n + 1))) 0 :=
  ⟨fun _ => ULift.up 0, by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact Fin.elim0 i⟩

def nonnegativeZeroAllowedWeight (n k : ℕ) (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ)) :
    {v : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent (Fin (n + 1)) (k : ℤ) //
      v.IsAllowedOn (fun _ : Fin 1 => (0 : Fin (n + 1)))} :=
  ⟨e.val, fun i hi => (not_lt_of_ge (e.property i) hi).elim⟩

def projectiveNonnegativeWeightZeroCycle (n k : ℕ) (j : Fin (n + 1))
    (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ)) (r : Γ(Spec (CommRingCat.of ℂ), ⊤)) :
    SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := ℂ) (σ := Fin (n + 1)) (k : ℤ) :=
  SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeightInclusion (R := ℂ) (k : ℤ) e.val
    ((SheafCohomology.Projective.OrderedCechZeroCycles.orderedEmptySupportCyclesEquiv Γ(Spec (CommRingCat.of ℂ), ⊤)
      e.val.liftedNegativeSupport e.emptySupport (ULift.up j)).symm r)

theorem projectiveNonnegativeWeightZeroCycle_factor (n k : ℕ) (j : Fin (n + 1))
    (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ)) (r : Γ(Spec (CommRingCat.of ℂ), ⊤)) :
    LaurentOrderedFactors.Dolbeault.algebraicHomogeneousLaurentFactorProjection (R := ℂ) (k : ℤ) 0
      (projectiveOrderedZeroTuple n)
      (projectiveNonnegativeWeightZeroCycle n k j e r).val =
        AddMonoidAlgebra.single (nonnegativeZeroAllowedWeight n k e) r := by
  have h := Laurent.WeightInclusionFactors.Dolbeault.algebraicLaurentWeightInclusion_factor (R := ℂ) (k : ℤ) e.val 0
    (projectiveOrderedZeroTuple n)
    (nonnegativeZeroAllowedWeight n k e).property
    (((SheafCohomology.Projective.OrderedCechZeroCycles.orderedEmptySupportCyclesEquiv Γ(Spec (CommRingCat.of ℂ), ⊤)
      e.val.liftedNegativeSupport e.emptySupport (ULift.up j)).symm r).val)
  exact h.trans (congrArg (AddMonoidAlgebra.single (nonnegativeZeroAllowedWeight n k e))
    (OrderedEmptySupportValues.Cech.orderedEmptySupportCyclesEquiv_symm_value Γ(Spec (CommRingCat.of ℂ), ⊤)
      e.val.liftedNegativeSupport e.emptySupport (ULift.up j) r
      (projectiveOrderedZeroTuple n)))

theorem projectiveLaurentOriginalComparison_zero_nonnegative_weight (n k : ℕ) (j : Fin (n + 1))
    (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ)) (r : Γ(Spec (CommRingCat.of ℂ), ⊤)) :
    ZeroCoefficientValues.Dolbeault.projectiveTwistZeroCoefficient n j (k : ℤ)
      ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j (k : ℤ)).f 0
        (projectiveNonnegativeWeightZeroCycle n k j e r).val) =
      PositiveAnalyticMonomial.Dolbeault.positiveAnalyticMonomial (n + 1) k e ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r) := by
  apply ZeroCoefficientValues.Dolbeault.projectiveTwistZeroCoefficient_of_cone_values
  intro x
  let t : Fin 1 → Fin (n + 1) := fun _ => 0
  have ht : StrictMono t := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact Fin.elim0 i
  let l := (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv t (k : ℤ)).symm (nonnegativeZeroAllowedWeight n k e)
  have hl : SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv t (k : ℤ) l = nonnegativeZeroAllowedWeight n k e :=
    (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv t (k : ℤ)).apply_symm_apply _
  have hb := (projectiveNonnegativeWeightZeroCycle_factor n k j e r).trans
    (congrArg (fun v => AddMonoidAlgebra.single v r) hl.symm)
  have h := LaurentModelMonomial.Dolbeault.projectiveLaurentOriginalComparison_monomial n j (k : ℤ) 0
    (projectiveNonnegativeWeightZeroCycle n k j e r).val t ht x l r hb
  have hp := congrArg (fun v : {v : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent (Fin (n + 1)) (k : ℤ) // v.IsAllowedOn t} =>
    ∏ i, x.val i ^ v.val.val i) hl
  exact h.trans ((congrArg ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r * ·) hp).trans
    (PositiveAnalyticMonomial.Dolbeault.positiveAnalyticMonomial_inverse_apply (n + 1) k e ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r) x.val).symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveWeightCoefficient.Dolbeault
