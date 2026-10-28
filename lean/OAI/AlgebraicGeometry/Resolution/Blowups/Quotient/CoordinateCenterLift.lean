import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientFrameBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.FrameCenterPermissibility
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Coordinate Center Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.CoordinateCenterLift.Construction

noncomputable section

/-! Finite dual-coordinate centers lift from the actual normal quotient without a chosen retraction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem quotient_preimage_span_lifted_generators
    {R ι : Type*} [CommRing R] (z : R) (g : ι → R) :
    (Ideal.span (Set.range (fun i => Ideal.Quotient.mk (Ideal.span {z}) (g i)))).comap
      (Ideal.Quotient.mk (Ideal.span {z})) = Ideal.span (Set.range g) ⊔ Ideal.span {z} := by
  have hm : (Ideal.span (Set.range g)).map (Ideal.Quotient.mk (Ideal.span {z})) =
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk (Ideal.span {z}) (g i))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [← hm, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem quotient_coordinate_center_blowup_smooth
    {k R ι : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [Fintype ι] [DecidableEq ι] (z : R) (D : Derivation k R R) (hD : D z = 1)
    (g : ι → R ⧸ Ideal.span {z})
    (δ : ι → Derivation k (R ⧸ Ideal.span {z}) (R ⧸ Ideal.span {z}))
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec ((Ideal.span (Set.range g)).comap (Ideal.Quotient.mk (Ideal.span {z}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  classical
  choose v hv using fun i => Ideal.Quotient.mk_surjective (g i)
  have he : (fun i => Ideal.Quotient.mk (Ideal.span {z}) (v i)) = g := funext hv
  rw [← he, quotient_preimage_span_lifted_generators]
  exact NormalQuotientFrameBlowup.Construction.normal_quotient_frame_blowup_smooth z v D hD δ (by intro i j; rw [hv]; exact hδ i j)

theorem quotient_frame_coefficient_center_permissible
    (k : Type u) {R ι : Type u} {τ : Type*}
    [Field k] [CharZero k] [IsAlgClosed k] [CommRing R] [Algebra k R] [Algebra ℚ R]
    [Algebra.Smooth k R] [Fintype ι] [DecidableEq ι]
    (D : Derivation k R R) (z : R) (hD : D z = 1) (p : τ → R) (b : ℕ)
    (g : ι → R ⧸ Ideal.span {z})
    (δ : ι → Derivation k (R ⧸ Ideal.span {z}) (R ⧸ Ideal.span {z}))
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0)
    (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C)
    (hC : C ≤ (Ideal.span (Set.range g)) ^ b.factorial) :
    let K := Ideal.span (Set.range g)
    let I := K.comap (Ideal.Quotient.mk (Ideal.span {z}))
    Ideal.span (Set.range p) ≤ I ^ b ∧ Algebra.Smooth k (R ⧸ I) ∧
      Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let Q := R ⧸ Ideal.span {z}
  let K := Ideal.span (Set.range g)
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
  have hcomponents := (Blowups.Smooth.DualCenterPowerRoot.Construction.smooth_dual_center_weighted_iff k g δ hδ b
    (fun j => HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j.val)).mp hw
  have hperm : Ideal.span (Set.range p) ≤ I ^ b := by
    apply (HypersurfaceCoefficientTransform.Construction.span_order_iff_coordinateDerivativeFamilyIdeals D z hD p I hzI b).mpr
    intro j hj
    rw [hmap]
    exact hcomponents ⟨j, hj⟩
  let : Algebra.Smooth k (Q ⧸ K) := DualFrameCenterSmooth.Construction.dual_derivation_family_center_smooth g δ hδ
  let : Algebra.Smooth k (Q ⧸ I.map (Ideal.Quotient.mkₐ k (Ideal.span {z}))) := by
    change Algebra.Smooth k (Q ⧸ I.map (Ideal.Quotient.mk (Ideal.span {z})))
    rw [hmap]
    infer_instance
  refine ⟨hperm, ?_, quotient_coordinate_center_blowup_smooth z D hD g δ hδ⟩
  exact Algebra.Smooth.of_equiv (DoubleQuot.quotQuotEquivQuotOfLEₐ k
    ((Ideal.span_singleton_le_iff_mem I).mpr hzI))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.CoordinateCenterLift.Construction
