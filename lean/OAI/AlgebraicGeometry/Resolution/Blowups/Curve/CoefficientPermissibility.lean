import OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicCenterPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedGeneratorFamily

/-! # Coefficient Permissibility -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoefficientPermissibility.Construction

noncomputable section

/-! Smooth curve coefficient centers lift to actual permissible ambient ideals. -/

open _root_.CategoryTheory

universe u

variable (k : Type u) {R : Type u} {ι : Type*} [Field k] [IsAlgClosed k]
  [CommRing R] [Algebra k R] [Algebra ℚ R] [IsNoetherianRing R]

/-- A weighted coefficient bound at a smooth hypersurface center whose
actual blowup is an isomorphism gives the exact ambient permissibility bound.
No polynomial coordinate frame or principal generator is assumed. -/
theorem coefficient_center_permissible_of_isIso
    (D : Derivation k R R) (z : R) (hz : D z = 1) (p : ι → R) (b : ℕ)
    (I : Ideal R) (hzI : z ∈ I)
    [Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {z})))]
    [IsIso (ReesGrading.Construction.affineBlowupToSpec (I.map (Ideal.Quotient.mk (Ideal.span {z}))))]
    (hcoeff : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤
      (I.map (Ideal.Quotient.mk (Ideal.span {z}))) ^ b.factorial) :
    Ideal.span (Set.range p) ≤ I ^ b := by
  have hcomponents := (IsomorphicCenterPowerRoot.Construction.smooth_isIso_center_weighted_iff k
    (I.map (Ideal.Quotient.mk (Ideal.span {z}))) b
    (fun j => HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j.val)).mp hcoeff
  apply (HypersurfaceCoefficientTransform.Construction.span_order_iff_coordinateDerivativeFamilyIdeals D z hz p I hzI b).mpr
  intro j hj
  exact hcomponents ⟨j, hj⟩

/-- Any retained coefficient ideal above the fixed normal-generator family
selects a permissible ambient center under the same smooth-center hypotheses. -/
theorem coefficient_interval_center_permissible_of_isIso
    (D : Derivation k R R) (z : R) (hz : D z = 1) (p : ι → R) (b : ℕ)
    (I : Ideal R) (hzI : z ∈ I)
    [Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {z})))]
    [IsIso (ReesGrading.Construction.affineBlowupToSpec (I.map (Ideal.Quotient.mk (Ideal.span {z}))))]
    (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C)
    (hC : C ≤ (I.map (Ideal.Quotient.mk (Ideal.span {z}))) ^ b.factorial) :
    Ideal.span (Set.range p) ≤ I ^ b :=
  coefficient_center_permissible_of_isIso k D z hz p b I hzI (hlow.trans hC)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoefficientPermissibility.Construction
