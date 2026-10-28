import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialLeaves
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.ModelRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Smooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.Schedule
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointChartTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.UnitBoundaryPrincipalNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IntersectionCenters

/-! # Monomial Terminal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Low weights on the recorded boundary faces imply the actual monomial order locus is empty. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v t

theorem Boundary.MonomialTerminal.Construction.partialBoundaryMonomialExponents_sum_le {ι : Type v} {σ : Type t}
    [Fintype ι] [Fintype σ] (r : ι → Option σ) (a : ι → ℕ) :
    (∑ s, Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents r a s) ≤ ∑ j, a j := by
  classical
  unfold Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  cases r j <;> simp

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.monomial_differential_bound
    {k R : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    {ι : Type v} [Fintype ι] {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (a : ι → ℕ) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}) (∑ j, a j) = ⊤ := by
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  rw [M.boundary_monomial_ideal a]
  have hb := (Blowups.Etale.RelativeOrder.Construction.etale_relative_differential_top_iff (σ := M.indices) (K := k)
    ((Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := k) (Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents M.coordinate a)}).map M.map)
    (∑ s, Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents M.coordinate a s)).mpr
      (Blowups.Etale.MonomialLeaves.Construction.etaleCoordinateMonomial_differential_bound (S := R) (Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents M.coordinate a))
  have hle := Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k
    ((Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := k) (Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents M.coordinate a)}).map M.map)
    (Boundary.MonomialTerminal.Construction.partialBoundaryMonomialExponents_sum_le M.coordinate a)
  rw [hb] at hle
  exact top_le_iff.mp hle

theorem Boundary.MonomialTerminal.Construction.boundaryMonomial_ideal_remove_unit_labels
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
    (w : ι → R) (a : ι → ℕ) (S : Finset ι) (hu : ∀ j, j ∉ S → IsUnit (w j)) :
    Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} =
      Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (fun j : S => w j.val) (fun j => a j.val)} := by
  classical
  have hprod : LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a =
      (∏ j ∈ S, w j ^ a j) * ∏ j ∈ Finset.univ \ S, w j ^ a j :=
    (Finset.prod_mul_prod_compl S (fun j => w j ^ a j)).symm
  have hunit : IsUnit (∏ j ∈ Finset.univ \ S, w j ^ a j) := by
    apply IsUnit.prod_iff.mpr
    intro j hj
    exact (hu j (Finset.mem_sdiff.mp hj).2).pow (a j)
  rw [hprod, Ideal.span_singleton_mul_right_unit hunit]
  apply congrArg (fun x : R => Ideal.span {x})
  exact (Finset.prod_coe_sort S (fun j => w j ^ a j)).symm

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.monomial_bound_of_unit_complement
    {k R : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    {ι : Type v} [Fintype ι] {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (a : ι → ℕ) (S : Finset ι) (hu : ∀ j, j ∉ S → IsUnit (w j)) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a})
      (Boundary.MonomialSchedule.Construction.boundaryFaceWeight a S) = ⊤ := by
  rw [Boundary.MonomialTerminal.Construction.boundaryMonomial_ideal_remove_unit_labels w a S hu]
  let e : S ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  have h := (M.reindex e).monomial_differential_bound (fun j => a j.val)
  change Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
    (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (fun j : S => w j.val) (fun j => a j.val)})
    (∑ j : S, a j.val) = ⊤ at h
  simpa only [Finset.sum_coe_sort, Boundary.MonomialSchedule.Construction.boundaryFaceWeight] using h

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.monomial_point_order_bound
    {k R : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    {ι : Type v} [Fintype ι] {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (a : ι → ℕ) (p : PrimeSpectrum R) (S : Finset ι)
    (hS : ∀ j, w j ∈ p.asIdeal → j ∈ S) (b : ℕ) (hb : Boundary.MonomialSchedule.Construction.boundaryFaceWeight a S < b) :
    ¬ (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}).map (algebraMap R (Localization.AtPrime p.asIdeal)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ b := by
  classical
  obtain ⟨t, ht, hunit⟩ := UnitBoundaryPrincipalNeighborhood.Construction.exists_unit_boundary_principal_neighborhood
    (fun j : {j : ι // j ∉ S} => w j.val) p (fun j hj => j.property (hS j.val hj))
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime t p ht
  let A := Localization.Away t
  let γ : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  have hγ : γ.toRingHom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  let N := M.baseChange γ hγ
  have hu : ∀ j, j ∉ S → IsUnit (γ (w j)) := fun j hj => hunit ⟨j, hj⟩
  have hmap : (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}).map γ.toRingHom =
      Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (fun j => γ (w j)) a} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    simp only [LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement, map_prod, map_pow]
    rfl
  have hrel : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      ((Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}).map γ.toRingHom) (Boundary.MonomialSchedule.Construction.boundaryFaceWeight a S) = ⊤ := by
    rw [hmap]
    exact N.monomial_bound_of_unit_complement a S hu
  have hord : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal
      ((Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}).map γ.toRingHom) (Boundary.MonomialSchedule.Construction.boundaryFaceWeight a S) = ⊤ := by
    apply top_le_iff.mp
    rw [← hrel]
    exact Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k _ _
  have hpoint : p.asIdeal = Q.asIdeal.comap γ.toRingHom :=
    (congrArg PrimeSpectrum.asIdeal hQ).symm
  intro h
  have h' := (Blowups.Etale.PrimeOrderNaturality.Construction.etale_map_prime_order_iff γ.toRingHom hγ _ p.asIdeal Q.asIdeal hpoint b).mpr h
  exact DifferentialLocalBound.Construction.local_order_lt_of_differential_top _ (Boundary.MonomialSchedule.Construction.boundaryFaceWeight a S) hord Q.asIdeal
    (h'.trans (Ideal.pow_le_pow_right (by omega)))

theorem Boundary.Schedule.Construction.BoundaryFacesCover.monomial_order_bound
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {R : CommRingCat.{u}} [Algebra k R] {ι : Type v} [Fintype ι]
    {w : ι → R} {L : List (Finset ι)} (h : Boundary.Schedule.Construction.BoundaryFacesCover w L)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (a : ι → ℕ) (b : ℕ)
    (hbound : ∀ S ∈ L, Boundary.MonomialSchedule.Construction.boundaryFaceWeight a S < b) (p : PrimeSpectrum R) :
    ¬ (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}).map (algebraMap R (Localization.AtPrime p.asIdeal)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ b := by
  obtain ⟨S, hS, hw⟩ := h p
  obtain ⟨B⟩ := hboundary p
  have hB : B.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstance : Etale (Spec.map (CommRingCat.ofHom B.map.toRingHom)))
  have hpoint : p.asIdeal = B.point.asIdeal.comap B.map.toRingHom :=
    (congrArg PrimeSpectrum.asIdeal B.point_over).symm
  have hactive : ∀ j, B.map (w j) ∈ B.point.asIdeal → j ∈ S := by
    intro j hj
    apply hw j
    rw [hpoint]
    exact hj
  have hmap : (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}).map B.map.toRingHom =
      Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (fun j => B.map (w j)) a} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    simp only [LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement, map_prod, map_pow]
    rfl
  intro h
  have h' := (Blowups.Etale.PrimeOrderNaturality.Construction.etale_map_prime_order_iff B.map.toRingHom hB _ p.asIdeal B.point.asIdeal hpoint b).mpr h
  rw [hmap] at h'
  exact B.model.monomial_point_order_bound a B.point S hactive b (hbound S hS) h'

theorem Boundary.Schedule.Construction.BoundaryFacesCover.monomial_terminal
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {R : CommRingCat.{u}} [Algebra k R] [Algebra.Smooth k R]
    {ι : Type v} [Fintype ι] {w : ι → R} {L : List (Finset ι)} (h : Boundary.Schedule.Construction.BoundaryFacesCover w L)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (a : ι → ℕ) (b : ℕ) (hb : 0 < b)
    (hbound : ∀ S ∈ L, Boundary.MonomialSchedule.Construction.boundaryFaceWeight a S < b) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}) (b - 1) = ⊤ := by
  apply (Blowups.Smooth.ClosedPointChartTransport.Construction.smooth_relative_differential_bound_iff_closedPoint_bound k _ (b - 1)).mpr
  intro q _
  simpa only [Nat.sub_add_cancel hb] using
    h.monomial_order_bound hboundary a b hbound ⟨q, inferInstance⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
