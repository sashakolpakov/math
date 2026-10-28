import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.DualFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.UnitOpenLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateLiftChoice
import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.CoordinateIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DerivationHom

/-! # Modeled Boundary Center Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.ModeledBoundaryCenterLift.Construction

noncomputable section

/-! Common boundary and center coordinates lift from a smooth normal quotient to actual ambient opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem quotient_modeled_boundary_center_lifts_to_open
    {k : Type u} [Field k] (R : CommRingCat.{u}) {Q : Type u} [CommRing Q]
    [Algebra k R] [Algebra k Q] [Algebra.Smooth k R]
    (q : R →ₐ[k] Q) (hq : Function.Surjective q) (z : R)
    (hker : RingHom.ker q.toRingHom = Ideal.span {z})
    (D : Derivation k R R) (hDz : D z = 1)
    {β : Type v} [Fintype β] (w : β → R)
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k Q β (fun j => q (w j))) (C : Finset M.indices)
    (F : Finset β) (hF : ∀ j, j ∈ F ↔ ∃ i ∈ C, M.coordinate j = some i)
    (p : PrimeSpectrum R) (hzp : z ∈ p.asIdeal) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R
      (((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map).comap q.toRingHom) w F p) := by
  classical
  let K := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map
  let I := K.comap q.toRingHom
  have hqp : RingHom.ker q.toRingHom ≤ p.asIdeal := by
    rw [hker]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hzp
  choose b hb using fun j => hq (M.multiplier j)
  let a (j : β) : R := match M.coordinate j with | none => w j | some _ => b j
  have hqa (j : β) : q (a j) = M.multiplier j := by
    cases hj : M.coordinate j with
    | none => simpa only [a, hj, mul_one] using M.equation j
    | some i => simpa only [a, hj] using hb j
  have hqu (j : β) : IsUnit (q (a j)) := by
    rw [hqa]
    exact M.multiplierUnit j
  obtain ⟨A, hAk, f, hf, P, hP, hau, q', hq', hcomm, hker'⟩ :=
    UnitOpenLift.Construction.quotient_unit_pointed_open_lift q hq a hqu p hqp
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hf
  have hfEt : f.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom f.toRingHom)).mp inferInstance
  let : Algebra.Smooth k A := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k f hfEt
  have hq'f (r : R) : q' (f r) = q r := AlgHom.congr_fun hcomm r
  have hkerA : RingHom.ker q'.toRingHom = Ideal.span {f z} := by
    rw [hker', hker, Ideal.map_span, Set.image_singleton]
    rfl
  let D' : Derivation k A A := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hfEt f.commutes D
  have hD'z : D' (f z) = 1 := by
    change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hfEt f.commutes D (f.toRingHom z) = 1
    rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hDz, map_one]
  have hqz : q' (f z) = 0 := by
    have hmem : f z ∈ RingHom.ker q'.toRingHom := by
      rw [hkerA]
      exact Ideal.mem_span_singleton_self _
    exact hmem
  have hwe (j : β) : q' (f (w j)) = q' (f (a j)) *
      match M.coordinate j with | none => 1 | some i => M.map (MvPolynomial.X i) := by
    rw [hq'f, hq'f, hqa]
    cases hj : M.coordinate j <;> simpa only [hj] using M.equation j
  obtain ⟨g, hg, hwg⟩ := Boundary.CoordinateLiftChoice.Construction.exists_boundary_preserving_coordinate_lifts q'.toRingHom hq'
    (fun i => M.map (MvPolynomial.X i)) (fun j => f (w j)) (fun j => f (a j)) hau
    M.coordinate M.distinct (fun j => by
      convert hwe j using 1; cases M.coordinate j <;> rfl)
    (fun j hj => by simp only [a, hj])
  change ∀ i, q' (g i) = M.map (MvPolynomial.X i) at hg
  let : Algebra (MvPolynomial M.indices k) Q := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) Q := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) Q :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  let δ : M.indices → Derivation k Q Q := fun i => Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) i
  have hδ (i j : M.indices) : δ i (q' (g j)) = if i = j then 1 else 0 := by
    rw [hg]
    exact Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X i j
  have hkerP : RingHom.ker q'.toRingHom ≤ P.asIdeal := by
    rw [hkerA]
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change z ∈ P.asIdeal.comap f.toRingHom
    have heP : P.asIdeal.comap f.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hP
    rw [heP]
    exact hzp
  obtain ⟨B, hBk, hBs, t, ht, P', hP', E, hE⟩ :=
    NormalQuotientOpenFrame.Construction.quotient_dual_frame_lifts_to_pointed_open q' hq' (f z) hqz D' hD'z g δ hδ P hkerP
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom t.toRingHom)) := ht
  let v := AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g (f z)
  let C' := insert none (C.image some)
  have hIA : I.map f.toRingHom = Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal v C' := by
    rw [CoordinateIdeal.Construction.quotient_center_map_of_kernel_square q.toRingHom q'.toRingHom f.toRingHom
      hq hq' (congrArg AlgHom.toRingHom hcomm) hker']
    have hK : K = Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal (fun i => q' (g i)) C := by
      simp only [K, SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal, Ideal.map_span, ← Set.image_comp,
        Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal, hg]
      rfl
    rw [hK]
    exact CoordinateIdeal.Construction.quotient_preimage_coordinate_family q'.toRingHom hq' (f z) hkerA g C
  let e (j : β) : Option (Option M.indices) := (M.coordinate j).map some
  have he : ∀ i j s, e i = some s → e j = some s → i = j := by
    intro i j s hi hj
    cases hi' : M.coordinate i with
    | none => simp [e, hi'] at hi
    | some l =>
        cases hj' : M.coordinate j with
        | none => simp [e, hj'] at hj
        | some m =>
            have hlm : l = m := Option.some.inj (Option.some.inj
              ((by simpa only [e, hi', Option.map_some] using hi : some (some l) = some s).trans
                (by simpa only [e, hj', Option.map_some] using hj : some (some m) = some s).symm))
            exact M.distinct i j l hi' (hj'.trans (congrArg some hlm.symm))
  have hwB (j : β) : t (f (w j)) = t (f (a j)) *
      match e j with | none => 1 | some i => t (v i) := by
    rw [hwg, map_mul]
    cases hj : M.coordinate j <;> simp only [e, hj, Option.map_none, Option.map_some, map_one, v,
      AdaptedEtaleFrame.Construction.transverseExtendedCoordinates]
  have hF' (j : β) : j ∈ F ↔ ∃ i ∈ C', e j = some i := by
    rw [hF]
    cases hj : M.coordinate j <;> simp [e, hj, C']
  obtain ⟨L⟩ := MixedBoundary.DualFrame.Construction.mixed_boundary_chart_of_dual_frame B (fun i => t (v i)) E hE C'
    (fun j => t (f (w j))) (fun j => t (f (a j))) (fun j => (hau j).map t.toRingHom)
    e he (fun j => by cases hj : e j <;> simpa only [hj] using hwB j) F hF' P'
  have hIB : (I.map f.toRingHom).map t.toRingHom =
      Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal (fun i => t (v i)) C' := by
    rw [hIA, CoordinateIdeal.Construction.coordinateFamilyIdeal_map]
    rfl
  have L' : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k B ((I.map f.toRingHom).map t.toRingHom)
      (fun j => t (f (w j))) F P' := by
    rw [hIB]
    exact L
  exact ⟨(L'.comp (I.map f.toRingHom) (fun j => f (w j)) F t P hP').comp I w F f p hP⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.ModeledBoundaryCenterLift.Construction
