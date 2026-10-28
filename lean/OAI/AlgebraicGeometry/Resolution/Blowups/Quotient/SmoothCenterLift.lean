import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.CoordinateCenterLift

/-! # Smooth Center Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.SmoothCenterLift.Construction

noncomputable section

/-! Every permissible smooth coefficient center lifts to an actual permissible smooth ambient center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem quotient_smooth_coefficient_center_permissible
    (k : Type u) {R : Type u} {τ : Type*}
    [Field k] [CharZero k] [IsAlgClosed k] [CommRing R] [Algebra k R] [Algebra ℚ R]
    [Algebra.Smooth k R]
    (D : Derivation k R R) (z : R) (hD : D z = 1) (p : τ → R) (b : ℕ)
    (K : Ideal (R ⧸ Ideal.span {z})) [Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ K)]
    (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C)
    (hC : C ≤ K ^ b.factorial) :
    let I := K.comap (Ideal.Quotient.mk (Ideal.span {z}))
    Ideal.span (Set.range p) ≤ I ^ b ∧ Algebra.Smooth k (R ⧸ I) ∧
      Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let Q := R ⧸ Ideal.span {z}
  let I := K.comap (Ideal.Quotient.mk (Ideal.span {z}))
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : Algebra.Smooth k Q := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
  have hzI : z ∈ I := by
    change Ideal.Quotient.mk (Ideal.span {z}) z ∈ K
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)]
    exact K.zero_mem
  have hmap : I.map (Ideal.Quotient.mk (Ideal.span {z})) = K :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective K
  have hw : WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j => HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j.val) ≤ K ^ b.factorial :=
    hlow.trans hC
  have hcomponents := (Blowups.Smooth.CenterPowerRoot.Construction.smooth_center_weighted_iff k K b
    (fun j => HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j.val)).mp hw
  have hperm : Ideal.span (Set.range p) ≤ I ^ b := by
    apply (HypersurfaceCoefficientTransform.Construction.span_order_iff_coordinateDerivativeFamilyIdeals D z hD p I hzI b).mpr
    intro j hj
    rw [hmap]
    exact hcomponents ⟨j, hj⟩
  let : Algebra.Smooth k (Q ⧸ I.map (Ideal.Quotient.mkₐ k (Ideal.span {z}))) := by
    change Algebra.Smooth k (Q ⧸ I.map (Ideal.Quotient.mk (Ideal.span {z})))
    rw [hmap]
    infer_instance
  let : Algebra.Smooth k (R ⧸ I) := Algebra.Smooth.of_equiv (DoubleQuot.quotQuotEquivQuotOfLEₐ k
    ((Ideal.span_singleton_le_iff_mem I).mpr hzI))
  exact ⟨hperm, inferInstance, Blowups.Smooth.AffineCenterBlowup.Construction.smooth_affine_center_blowup_smooth I⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.SmoothCenterLift.Construction
