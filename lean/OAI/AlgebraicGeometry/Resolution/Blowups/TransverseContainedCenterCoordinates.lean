import OAI.AlgebraicGeometry.Resolution.Blowups.TransverseContainedCenterPivot
import OAI.AlgebraicGeometry.Resolution.Blowups.ReplacedCenterCoordinateIndices
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateReplacement
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativePartialBaseChange

/-! # Transverse Contained Center Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TransverseContainedCenterCoordinates.Construction

noncomputable section

/-! Actual common coordinates for a contained transverse hypersurface and a boundary-compatible center. -/

universe u

/-- A principal neighborhood retains the original center exactly, makes
the contained hypersurface a center coordinate, and preserves every other
coordinate. The replaced coordinate lies outside the entire active boundary. -/
theorem exists_transverse_contained_center_coordinates
    {σ k R : Type u} [Field k] [CommRing R] [Fintype σ] [DecidableEq σ]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R]
    (C B : Finset σ) (q : Ideal R) [q.IsPrime]
    (hC : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := R) C ≤ q)
    (hB : ∀ i ∈ B, algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈ q)
    (z : R) (hz : z ∈ Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := R) C)
    (E : Derivation k R R)
    (hE : ∀ i ∈ B, E (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) ∈
      Ideal.span {algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)})
    (hEz : E z ∉ q) :
    ∃ (f : R) (i : C), f ∉ q ∧ i.val ∉ B ∧
      ∃ φ : MvPolynomial (Option {j : σ // i.val ≠ j}) k →ₐ[k] Localization.Away f,
        φ.toRingHom.Etale ∧ φ (MvPolynomial.X none) = algebraMap R (Localization.Away f) z ∧
        (∀ j : {j : σ // i.val ≠ j}, φ (MvPolynomial.X (some j)) =
          algebraMap R (Localization.Away f) (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val))) ∧
        (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := R) C).map (algebraMap R (Localization.Away f)) =
          (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (Finset.univ.image (ReplacedCenterCoordinateIndices.Construction.centerReplacementCoordinateEmbedding C i))).map φ.toRingHom := by
  classical
  obtain ⟨i, c, hiB, hc, hci, hDi⟩ := TransverseContainedCenterPivot.Construction.exists_transverse_contained_center_pivot C B q hC hB z hz E hE hEz
  let f := c i * Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i.val z
  have hf : f ∉ q := q.primeCompl.mul_mem hci hDi
  let A := Localization.Away f
  let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway f
  let : Algebra.Etale (MvPolynomial σ k) A := Algebra.Etale.comp (MvPolynomial σ k) R A
  have hu : IsUnit (algebraMap R A (c i) *
      algebraMap R A (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i.val z)) := by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit f
  have hupartial : IsUnit (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := A) i.val (algebraMap R A z)) := by
    rw [Blowups.Etale.RelativePartialBaseChange.Construction.etaleRelativePartial_baseChange (S := R) (T := A)]
    exact isUnit_of_mul_isUnit_right hu
  let φ : MvPolynomial (Option {j : σ // i.val ≠ j}) k →ₐ[k] A :=
    Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap i.val (algebraMap R A z)
  have hzero : φ (MvPolynomial.X none) = algebraMap R A z :=
    Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_none i.val (algebraMap R A z)
  have hrest (j : {j : σ // i.val ≠ j}) : φ (MvPolynomial.X (some j)) =
      algebraMap R A (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) := by
    rw [Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_some]
    exact IsScalarTower.algebraMap_apply (MvPolynomial σ k) R A (MvPolynomial.X j.val)
  refine ⟨f, i, hf, hiB, φ, Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_etale i.val _ hupartial, hzero, hrest, ?_⟩
  let g : C → A := fun j => algebraMap R A (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val))
  have hc' : (∑ j, algebraMap R A (c j) * g j) = algebraMap R A z := by
    simpa only [map_sum, map_mul] using congrArg (algebraMap R A) hc
  have hgen : (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := R) C).map (algebraMap R A) =
      Ideal.span (Set.range g) := by
    have hroot : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := R) C =
        Ideal.span (Set.range (fun j : C => algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val))) :=
      Coordinate.CenterPermissibility.Construction.etaleSubsetCoordinateIdeal_eq_span (K := k) (S := R) C
    have h := congrArg (fun I : Ideal R => I.map (algebraMap R A)) hroot
    rw [Ideal.map_span, ← Set.range_comp] at h
    exact h
  have hrep := CenterGeneratorReplacement.Construction.centerReplacementFamily_span g (fun j => algebraMap R A (c j)) i
    (algebraMap R A z) hc' (isUnit_of_mul_isUnit_left hu)
  have hcoord := ReplacedCenterCoordinateIndices.Construction.replaced_center_coordinate_ideal C i
    (fun j => algebraMap R A (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)))
    (algebraMap R A z) φ.toRingHom hzero hrest
  exact hgen.trans (hrep.symm.trans hcoord.symm)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TransverseContainedCenterCoordinates.Construction
