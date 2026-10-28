import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Reindex
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IntersectionCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.PartialLabelTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ChartEtaleBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Component

/-! # Boundary Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Ambient coefficient component centers preserve the full transverse boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.normal_center
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} (w : ι → R) (z : R)
    (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R (fun j : Option ι => match j with | none => z | some j => w j)) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R (Ideal.span {z}) w ∅ := by
  classical
  let v : Option ι → R := fun j => match j with | none => z | some j => w j
  have heq : Boundary.CountReduction.Construction.boundaryIntersectionIdeal v {none} = Ideal.span {z} := by
    have hrange : Set.range (fun j : ({none} : Finset (Option ι)) => v j.val) = {z} := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        have hj : j.val = none := Finset.mem_singleton.mp j.property
        simp only [hj, v, Set.mem_singleton_iff]
      · intro hx
        exact ⟨⟨none, Finset.mem_singleton_self none⟩, (Set.mem_singleton_iff.mp hx).symm⟩
    exact congrArg Ideal.span hrange
  have hc := h.intersection_center {none}
  rw [heq] at hc
  exact hc.pullbackLabels (fun j : ι => some (some j))
    (by intro i j s hi hj; exact Option.some_injective ι (Option.some_injective (Option ι) (hi.trans hj.symm)))
    w (fun _ => 1) (fun _ => isUnit_one) (by intro j; exact (one_mul (w j)).symm)
    ∅ (by intro j; simp)

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.idempotent_hypersurface_center
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} (w : ι → R) (z : R)
    (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R (fun j : Option ι => match j with | none => z | some j => w j))
    (I : Ideal R) (r : R) (hr : r ∈ I)
    (hI : I = Ideal.span {r} ⊔ Ideal.span {z}) (hrel : r * (1 - r) ∈ Ideal.span {z}) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w ∅ := by
  intro p hp
  have hne : 1 - r ∉ p.asIdeal := by
    intro ht
    have hsum := p.asIdeal.add_mem (hp hr) ht
    exact p.asIdeal.one_notMem (by simpa only [add_sub_cancel] using hsum)
  let S := Localization.Away (1 - r)
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  have hf : f.toRingHom.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (1 - r))
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := IsOpenImmersion.of_isLocalization (1 - r)
  obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime (1 - r) p hne
  have hm : I.map f.toRingHom = Ideal.span {f z} := IdempotentQuotientCenter.Construction.idempotent_quotient_center_map_complement I r z hI hrel
  have hb : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of S)
      (fun j : Option ι => match j with | none => f z | some j => f (w j)) := by
    convert h.etale_baseChange (S := .of S) f hf using 1
    funext j
    cases j <;> rfl
  have hc : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k (.of S) (I.map f.toRingHom) (fun j => f (w j)) ∅ := by
    rw [hm]
    exact LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.normal_center (R := .of S) (fun j => f (w j)) (f z) hb
  have hIp : I.map f.toRingHom ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    have hpoint := congrArg PrimeSpectrum.asIdeal hq
    exact hp.trans_eq hpoint.symm
  obtain ⟨C⟩ := hc q hIp
  exact ⟨C.comp (S := .of S) I w ∅ f p hq⟩

theorem Component.BoundaryCenter.Construction.coefficientComponentCenter_boundary_admissible
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {R : CommRingCat.{u}} [Algebra k R] {ι : Type v}
    (w : ι → R) (z : R) (J : Ideal R) (b : ℕ)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})]
    (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R (fun j : Option ι => match j with | none => z | some j => w j)) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R (Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z J b) w ∅ := by
  obtain ⟨r, hr, hI, hrel⟩ := Coefficient.Component.Construction.coefficientComponentCenter_generators k z J b
  exact h.idempotent_hypersurface_center w z _ r hr hI hrel

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem Component.BoundaryCenter.Construction.coefficientComponentCenter_blowup_boundary
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {R : CommRingCat.{u}} [Algebra k R] {ι : Type v}
    (w : ι → R) (z : R) (J : Ideal R) (b : ℕ)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})]
    (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R (fun j : Option ι => match j with | none => z | some j => w j))
    (a : Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z J b) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart _ a))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily _ a ∅ w (by simp)) := by
  have hb : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w := h.reindex ⟨some, Option.some_injective ι⟩
  exact MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup R _ w ∅ (by simp) hb
    (Component.BoundaryCenter.Construction.coefficientComponentCenter_boundary_admissible w z J b h) a

end

end OAI.AlgebraicGeometry.Resolution.Blowups
