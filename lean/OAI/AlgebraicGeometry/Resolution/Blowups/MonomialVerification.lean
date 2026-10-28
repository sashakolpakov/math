import OAI.AlgebraicGeometry.Resolution.Blowups.MonomialTree
import OAI.AlgebraicGeometry.Resolution.Blowups.SubsetMonomialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCoordinateBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrderLocus
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedOrder

/-! # Monomial Verification -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Verifying finite monomial resolution trees against actual proper blowups and local order at their leaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {σ K : Type u} [Fintype σ] [Field K] [CharZero K] [IsAlgClosed K]

omit [CharZero K] [IsAlgClosed K] in
theorem MonomialVerification.Construction.coordinateMonomial_ne_zero (a : σ → ℕ) : MonomialBlowupChart.Construction.coordinateMonomial (R := K) a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact pow_ne_zero _ (X_ne_zero j)

omit [CharZero K] [IsAlgClosed K] in
theorem MonomialVerification.Construction.coordinateMonomial_totalDegree_le (a : σ → ℕ) :
    (MonomialBlowupChart.Construction.coordinateMonomial (R := K) a).totalDegree ≤ ∑ j, a j := by
  simpa only [MonomialBlowupChart.Construction.coordinateMonomial, totalDegree_X_pow] using
    totalDegree_finsetProd Finset.univ (fun j => (X j : MvPolynomial σ K) ^ a j)

variable [DecidableEq σ]

/-- A leaf's exponent bound excludes the order locus at every closed point
of its actual affine space. -/
theorem MonomialVerification.Construction.coordinateMonomial_leaf_order (a : σ → ℕ) (b : ℕ) (hb : (∑ j, a j) < b)
    (q : Ideal (MvPolynomial σ K)) [q.IsMaximal] :
    ¬ (Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := K) a}).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b := by
  intro h
  let J : Ideal (MvPolynomial σ K) := Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}
  have hd : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J (∑ j, a j) = ⊤ :=
    DifferentialOrderLocus.Construction.iteratedDifferentialIdeal_eq_top_of_degree_bound (∑ j, a j) J (MonomialBlowupChart.Construction.coordinateMonomial a)
      (MonomialVerification.Construction.coordinateMonomial_totalDegree_le a) (Ideal.mem_span_singleton_self _) (MonomialVerification.Construction.coordinateMonomial_ne_zero a)
  have hl := (Etale.ClosedOrder.Construction.etale_closedPoint_order_iff_differentialIdeal (σ := σ) (K := K) J q (∑ j, a j)).mp
    (h.trans (Ideal.pow_le_pow_right (by omega)))
  rw [hd] at hl
  exact (show q.IsMaximal from inferInstance).ne_top (top_le_iff.mp hl)

/-- A verification predicate for the local tree: its nodes are proper
smooth-ambient blowups with the stated actual controlled ideals, and every
leaf has empty closed-point order locus at the prescribed control. -/
def MonomialTree.Construction.MonomialResolutionTree.VerifiedOver (K : Type u) [Field K]
    {b : ℕ} {a : σ → ℕ} : MonomialTree.Construction.MonomialResolutionTree b a → Prop
  | .done a _ => ∀ (q : Ideal (MvPolynomial σ K)) [q.IsMaximal],
      ¬ (Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}).map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b
  | .blowup a C _ children =>
      Algebra.Smooth K (Blowups.Smooth.SubsetCenter.Construction.subsetCoordinateCenterRing (R := K) C) ∧
      IsProper (ReesGrading.Construction.affineBlowupToSpec (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := K) C)) ∧
      Smooth (ReesGrading.Construction.affineBlowupToSpec (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := K) C) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial σ K))) ∧
      (∀ i : C,
        (ControlledTransform.Construction.blowupControlledTransform (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := K) C)
          (Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}) b (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i)).map
            (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial C i) =
          Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := K) (MonomialTermination.Construction.monomialChartExponents a b C i.val)}) ∧
      ∀ i : C, (children i).VerifiedOver K

/-- Every tree assembled from minimal coordinate centers satisfies its
geometric and ideal-theoretic verification conditions. -/
theorem MonomialTree.Construction.MonomialResolutionTree.verifiedOver {b : ℕ} {a : σ → ℕ} (T : MonomialTree.Construction.MonomialResolutionTree b a) :
    T.VerifiedOver K := by
  induction T with
  | done a ha => exact MonomialVerification.Construction.coordinateMonomial_leaf_order a b ha
  | blowup a C hC children ih =>
    exact ⟨Blowups.Smooth.SubsetCenter.Construction.subsetCoordinateCenter_smooth C, inferInstance, Blowups.Smooth.SubsetCoordinateBlowup.Construction.subsetCoordinateBlowup_smooth C,
      fun i => SubsetMonomialTransform.Construction.subsetCoordinateMonomial_controlledIdeal a b C hC.2.1 i, ih⟩

/-- A finite verified local monomial resolution exists for every positive
control. This is a tree of actual affine blowup charts; it does not assert
that independently chosen centers on overlapping charts glue globally. -/
theorem MonomialVerification.Construction.exists_verified_local_monomial_resolution (b : ℕ) (hb : 0 < b) (a : σ → ℕ) :
    ∃ T : MonomialTree.Construction.MonomialResolutionTree b a, T.height ≤ ∑ j, a j ∧ T.VerifiedOver K :=
  ⟨MonomialTree.Construction.monomialResolutionTree b hb a, MonomialTree.Construction.MonomialResolutionTree.height_le _,
    MonomialTree.Construction.MonomialResolutionTree.verifiedOver _⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
