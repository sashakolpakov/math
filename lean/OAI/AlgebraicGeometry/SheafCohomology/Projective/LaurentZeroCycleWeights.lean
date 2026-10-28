import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeightAssembly
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechZeroCycles

/-! # Laurent Zero Cycle Weights -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial

noncomputable section

/-! Weight components and inclusions on degree-zero Laurent cycles. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechZeroCycles
universe u
open _root_.MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]
local instance laurentZeroWeightDecidableEq : DecidableEq σ := Classical.decEq σ

abbrev LaurentZeroCycles (d : ℤ) :=
  ((LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d 0).hom).ker

def laurentZeroCycleWeight (d : ℤ) (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
    LaurentZeroCycles (R := R) (σ := σ) d →ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      (OrderedCechSupportContraction.orderedCechSupportDifferential Γ(Spec (CommRingCat.of R), ⊤)
        e.liftedNegativeSupport 0).ker :=
  ((TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent (R := R) d e 0).comp
    (LaurentZeroCycles (R := R) (σ := σ) d).subtype).codRestrict _ (fun z => by
      change OrderedCechSupportContraction.orderedCechSupportDifferential Γ(Spec (CommRingCat.of R), ⊤)
        e.liftedNegativeSupport 0
        (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent (R := R) d e 0 z.val) = 0
      rw [← TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_differential, z.property, map_zero])

def laurentZeroCycleWeightInclusion (d : ℤ) (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
    (OrderedCechSupportContraction.orderedCechSupportDifferential Γ(Spec (CommRingCat.of R), ⊤)
      e.liftedNegativeSupport 0).ker →ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
        LaurentZeroCycles (R := R) (σ := σ) d :=
  ((TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e 0).comp
    (OrderedCechSupportContraction.orderedCechSupportDifferential Γ(Spec (CommRingCat.of R), ⊤)
      e.liftedNegativeSupport 0).ker.subtype).codRestrict _ (fun z => by
      change (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d 0).hom
        (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e 0 z.val) = 0
      rw [TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion_differential, z.property, map_zero])

theorem laurentZeroCycleWeight_inclusion (d : ℤ) (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d)
    (z : (OrderedCechSupportContraction.orderedCechSupportDifferential Γ(Spec (CommRingCat.of R), ⊤)
      e.liftedNegativeSupport 0).ker) :
    laurentZeroCycleWeight (R := R) d e
      (laurentZeroCycleWeightInclusion (R := R) d e z) = z := by
  apply Subtype.ext
  exact TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_inclusion d e 0 z.val

theorem laurentZeroCycleWeight_inclusion_ne (d : ℤ)
    (e f : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) (hef : f ≠ e)
    (z : (OrderedCechSupportContraction.orderedCechSupportDifferential Γ(Spec (CommRingCat.of R), ⊤)
      e.liftedNegativeSupport 0).ker) :
    laurentZeroCycleWeight (R := R) d f
      (laurentZeroCycleWeightInclusion (R := R) d e z) = 0 := by
  apply Subtype.ext
  exact TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_inclusion_ne d e f hef 0 z.val

theorem laurentZeroCycleWeight_eq_zero_of_nonempty (d : ℤ) (hd : 0 ≤ d) (j : σ)
    (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d)
    (he : (e.liftedNegativeSupport : Set (ULift.{u} σ)) ≠ ∅)
    (z : LaurentZeroCycles (R := R) (σ := σ) d) :
    laurentZeroCycleWeight (R := R) d e z = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : ULift.{u} σ, i ∉ e.liftedNegativeSupport :=
    e.exists_not_mem_liftedNegativeSupport_of_nonneg j hd
  apply Subtype.ext
  apply OrderedCechSupportContraction.orderedCechSupportDifferential_zero_injective Γ(Spec (CommRingCat.of R), ⊤)
    e.liftedNegativeSupport (Set.nonempty_iff_ne_empty.mpr he) i hi
  exact (laurentZeroCycleWeight (R := R) d e z).property.trans (map_zero _).symm

theorem laurentZeroCycle_ext [Fintype σ] (d : ℤ)
    {z w : LaurentZeroCycles (R := R) (σ := σ) d}
    (h : ∀ e, laurentZeroCycleWeight (R := R) d e z = laurentZeroCycleWeight (R := R) d e w) :
    z = w := by
  apply Subtype.ext
  have hc (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
      TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent (R := R) d e 0 (z.val - w.val) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val (h e))
  apply sub_eq_zero.mp
  rw [← TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights_reconstruct d 0 (z.val - w.val)]
  simp only [hc, map_zero, Finset.sum_const_zero]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial
