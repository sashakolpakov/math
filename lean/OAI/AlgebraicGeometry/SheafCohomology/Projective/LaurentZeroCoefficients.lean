import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCycleWeights

/-! # Laurent Zero Coefficients -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial

noncomputable section

/-! Nonnegative Laurent weights give the coefficients of global positive twists. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
universe u
open _root_.MvPolynomial
variable {σ : Type}

def NonnegativeLaurentWeight (σ : Type) (d : ℤ) :=
  {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d // ∀ i, 0 ≤ e.val i}

theorem NonnegativeLaurentWeight.emptySupport {d : ℤ} (e : NonnegativeLaurentWeight σ d) :
    (e.val.liftedNegativeSupport : Set (ULift.{u} σ)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact (not_lt_of_ge (e.property i.down)) hi

instance nonnegativeLaurentWeightFinite [Fintype σ] (d : ℤ) :
    Finite (NonnegativeLaurentWeight σ d) := by
  have hsub : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d | ∀ i, 0 ≤ e.val i} ⊆
      {e | (e.liftedNegativeSupport : Set (ULift.{0} σ)) = ∅} := by
    intro e he
    exact NonnegativeLaurentWeight.emptySupport (⟨e, he⟩ : NonnegativeLaurentWeight σ d)
  exact ((LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_empty
    (σ := σ) d).subset hsub).to_subtype

instance nonnegativeLaurentWeightFintype [Fintype σ] (d : ℤ) :
    Fintype (NonnegativeLaurentWeight σ d) := Fintype.ofFinite _

variable {R : Type u} [CommRing R] [LinearOrder σ]
local instance laurentZeroCoefficientsDecidableEq : DecidableEq σ := Classical.decEq σ

def laurentZeroCoefficients (d : ℤ) (j : σ) :
    LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d →ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      (NonnegativeLaurentWeight σ d → Γ(Spec (CommRingCat.of R), ⊤)) :=
  LinearMap.pi fun e =>
    (OrderedCechZeroCycles.orderedEmptySupportCyclesEquiv Γ(Spec (CommRingCat.of R), ⊤)
      e.val.liftedNegativeSupport e.emptySupport (ULift.up j)).toLinearMap.comp
      (LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e.val)

def laurentZeroFromCoefficients [Fintype σ] (d : ℤ) (j : σ) :
    (NonnegativeLaurentWeight σ d → Γ(Spec (CommRingCat.of R), ⊤)) →ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)] LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d := by
  classical
  exact ∑ e : NonnegativeLaurentWeight σ d,
    (LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeightInclusion (R := R) d e.val).comp
      ((OrderedCechZeroCycles.orderedEmptySupportCyclesEquiv Γ(Spec (CommRingCat.of R), ⊤)
        e.val.liftedNegativeSupport e.emptySupport (ULift.up j)).symm.toLinearMap.comp
        (LinearMap.proj e))

theorem laurentZeroWeight_fromCoefficients [Fintype σ] (d : ℤ) (j : σ)
    (c : NonnegativeLaurentWeight σ d → Γ(Spec (CommRingCat.of R), ⊤))
    (e : NonnegativeLaurentWeight σ d) :
    LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e.val (laurentZeroFromCoefficients (R := R) d j c) =
      (OrderedCechZeroCycles.orderedEmptySupportCyclesEquiv Γ(Spec (CommRingCat.of R), ⊤)
        e.val.liftedNegativeSupport e.emptySupport (ULift.up j)).symm (c e) := by
  classical
  simp only [laurentZeroFromCoefficients, LinearMap.sum_apply, map_sum, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.proj_apply]
  rw [Finset.sum_eq_single e]
  · exact LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight_inclusion d e.val _
  · intro f _ hfe
    exact LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight_inclusion_ne d f.val e.val
      (fun h => hfe (Subtype.ext h.symm)) _
  · simp

theorem laurentZeroCoefficients_from [Fintype σ] (d : ℤ) (j : σ)
    (c : NonnegativeLaurentWeight σ d → Γ(Spec (CommRingCat.of R), ⊤)) :
    laurentZeroCoefficients (R := R) d j (laurentZeroFromCoefficients (R := R) d j c) = c := by
  funext e
  change OrderedCechZeroCycles.orderedEmptySupportCyclesEquiv Γ(Spec (CommRingCat.of R), ⊤)
      e.val.liftedNegativeSupport e.emptySupport (ULift.up j)
      (LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e.val (laurentZeroFromCoefficients (R := R) d j c)) = c e
  rw [laurentZeroWeight_fromCoefficients, LinearEquiv.apply_symm_apply]

theorem laurentZeroFrom_coefficients [Fintype σ] (d : ℤ) (hd : 0 ≤ d) (j : σ)
    (z : LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d) :
    laurentZeroFromCoefficients (R := R) d j (laurentZeroCoefficients (R := R) d j z) = z := by
  apply LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycle_ext d
  intro e
  by_cases he : ∀ i, 0 ≤ e.val i
  · let e' : NonnegativeLaurentWeight σ d := ⟨e, he⟩
    change LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e'.val
      (laurentZeroFromCoefficients (R := R) d j (laurentZeroCoefficients (R := R) d j z)) = _
    rw [laurentZeroWeight_fromCoefficients]
    exact (OrderedCechZeroCycles.orderedEmptySupportCyclesEquiv Γ(Spec (CommRingCat.of R), ⊤)
      e'.val.liftedNegativeSupport e'.emptySupport (ULift.up j)).symm_apply_apply _
  · have hn : (e.liftedNegativeSupport : Set (ULift.{u} σ)) ≠ ∅ := by
      intro h
      apply he
      intro i
      by_contra hi
      have hm : (ULift.up i : ULift.{u} σ) ∈ e.liftedNegativeSupport := by exact lt_of_not_ge hi
      rw [h] at hm
      exact hm
    rw [LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight_eq_zero_of_nonempty d hd j e hn,
      LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight_eq_zero_of_nonempty d hd j e hn]

def laurentZeroCyclesEquivCoefficients [Fintype σ] (d : ℤ) (hd : 0 ≤ d) (j : σ) :
    LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      (NonnegativeLaurentWeight σ d → Γ(Spec (CommRingCat.of R), ⊤)) :=
  { laurentZeroCoefficients (R := R) d j with
    invFun := laurentZeroFromCoefficients (R := R) d j
    left_inv := laurentZeroFrom_coefficients d hd j
    right_inv := laurentZeroCoefficients_from d j }

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial
