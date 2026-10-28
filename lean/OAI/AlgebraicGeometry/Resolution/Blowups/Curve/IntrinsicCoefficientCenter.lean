import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoefficientPermissibility
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFixedControlStep
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Intrinsic Coefficient Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicCoefficientCenter.Construction

noncomputable section

/-! An explicit smooth permissible ambient center chosen by curve coefficient induction. -/

open _root_.CategoryTheory

universe u

variable (k : Type u) {R : Type u} {ι : Type*} [Field k] [IsAlgClosed k]
  [CommRing R] [Algebra k R] [Algebra ℚ R] [IsNoetherianRing R]

/-- Curve coefficient induction selects an actual ambient center: the
preimage of the intrinsic coefficient tangent ideal. The center is smooth
and permissible at the original ambient control. -/
theorem curve_intrinsic_coefficient_center_lift
    (D : Derivation k R R) (z : R) (hz : D z = 1) (p : ι → R) (b n : ℕ)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 1)
    (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C)
    (hbn : b.factorial ≤ n + 1)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C (n + 1) = ⊤) :
    let K := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C n
    let I := K.comap (Ideal.Quotient.mk (Ideal.span {z}))
    z ∈ I ∧ Ideal.span (Set.range p) ≤ I ^ b ∧ Algebra.Smooth k (R ⧸ I) ∧
      C ≤ K ^ b.factorial ∧ IsIso (ReesGrading.Construction.affineBlowupToSpec K) := by
  let K := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C n
  let I := K.comap (Ideal.Quotient.mk (Ideal.span {z}))
  obtain ⟨hC, hsmooth, hπ, _⟩ := Affine.CurveFixedControlStep.Construction.affine_curve_fixed_control_step k hd C n b.factorial
    (Nat.factorial_pos b) hbn hbound
  have hmap : I.map (Ideal.Quotient.mk (Ideal.span {z})) = K :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective K
  have hzI : z ∈ I := by
    change Ideal.Quotient.mk (Ideal.span {z}) z ∈ K
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)]
    exact K.zero_mem
  let : Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {z}))) :=
    hmap.symm ▸ hsmooth
  let : IsIso (ReesGrading.Construction.affineBlowupToSpec (I.map (Ideal.Quotient.mk (Ideal.span {z})))) := hmap.symm ▸ hπ
  have hperm : Ideal.span (Set.range p) ≤ I ^ b :=
    CoefficientPermissibility.Construction.coefficient_interval_center_permissible_of_isIso k D z hz p b I hzI C hlow (hmap.symm ▸ hC)
  let : Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ I.map (Ideal.Quotient.mkₐ k (Ideal.span {z}))) := by
    change Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {z})))
    infer_instance
  have hambient : Algebra.Smooth k (R ⧸ I) :=
    Algebra.Smooth.of_equiv
      (DoubleQuot.quotQuotEquivQuotOfLEₐ k ((Ideal.span_singleton_le_iff_mem I).mpr hzI))
  exact ⟨hzI, hperm, hambient, hC, hπ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicCoefficientCenter.Construction
