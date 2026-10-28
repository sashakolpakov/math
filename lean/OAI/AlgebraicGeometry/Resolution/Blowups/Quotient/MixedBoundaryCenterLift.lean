import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.ModeledBoundaryCenterLift
import OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalOpenFactorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.PrincipalOpenLift
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.EquationCongruence
import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.BoundaryCenterOpenSquare

/-! # Mixed Boundary Center Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Boundary-compatible centers on a smooth normal quotient lift using actual ambient open charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem Quotient.MixedBoundaryCenterLift.Construction.quotient_mixed_boundary_center_chart_lifts
    {k : Type u} [Field k] (R Q : CommRingCat.{u})
    [Algebra k R] [Algebra k Q] [Algebra.Smooth k R]
    (q : R →ₐ[k] Q) (hq : Function.Surjective q) (z : R)
    (hker : RingHom.ker q.toRingHom = Ideal.span {z})
    (D : Derivation k R R) (hDz : D z = 1)
    {β : Type v} [Fintype β] (w : β → R) (K : Ideal Q) (F : Finset β)
    (p : PrimeSpectrum R) (pQ : PrimeSpectrum Q) (hpQ : PrimeSpectrum.comap q.toRingHom pQ = p)
    (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k Q K (fun j => q (w j)) F pQ) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R (K.comap q.toRingHom) w F p) := by
  classical
  obtain ⟨s, hs, g, hg, hgf⟩ := PrincipalOpenFactorization.Construction.exists_pointed_principal_open_factorization Q C.chart.carrier
    C.chart.map pQ C.chart.point C.chart.point_over
  obtain ⟨r, rfl⟩ := hq s
  let A := Localization.Away r
  let T := Localization.Away (q r)
  let f : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  let a : Q →ₐ[k] T := IsScalarTower.toAlgHom k Q T
  let q' : A →ₐ[k] T := Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap q r
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    IsOpenImmersion.of_isLocalization r
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) := hg
  have hgEt : g.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom g.toRingHom)).mp inferInstance
  let M := (C.chart.model.baseChange g hgEt).congrEquations (fun j => q' (f (w j))) (by
    intro j
    change Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap q r (algebraMap R A (w j)) = g (C.chart.map (q (w j)))
    rw [Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_constants]
    exact (AlgHom.congr_fun hgf (q (w j))).symm)
  have hK : K.map a.toRingHom = (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C.coordinates).map M.map := by
    have hmaps : g.toRingHom.comp C.chart.map.toRingHom = a.toRingHom := congrArg AlgHom.toRingHom hgf
    rw [← hmaps, ← Ideal.map_map, C.center_eq, Ideal.map_map]
    rfl
  have hr : r ∉ p.asIdeal := by
    have he : pQ.asIdeal.comap q.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpQ
    rw [← he]
    exact hs
  obtain ⟨P, hP⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r p hr
  have hker' : RingHom.ker q'.toRingHom = Ideal.span {f z} := by
    rw [Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_kernel, hker, Ideal.map_span, Set.image_singleton]
    rfl
  have hqz : q z = 0 := by
    have hz : z ∈ RingHom.ker q.toRingHom := by rw [hker]; exact Ideal.mem_span_singleton_self _
    exact hz
  have hzp : z ∈ p.asIdeal := by
    have he : pQ.asIdeal.comap q.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpQ
    rw [← he]
    change q z ∈ pQ.asIdeal
    rw [hqz]
    exact pQ.asIdeal.zero_mem
  have hI : (K.comap q.toRingHom).map f.toRingHom =
      ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C.coordinates).map M.map).comap q'.toRingHom := by
    exact (Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_center q hq r K).trans
      (congrArg (fun J : Ideal T => J.comap q'.toRingHom) hK)
  exact Quotient.BoundaryCenterOpenSquare.Construction.quotient_boundary_center_lift_on_open_square R (.of A) f q'
    (Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_surjective q hq r) z hker' D hDz w (K.comap q.toRingHom)
    M C.coordinates F C.divided_iff hI p hzp P hP

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.quotientLift
    {k : Type u} [Field k] (R Q : CommRingCat.{u})
    [Algebra k R] [Algebra k Q] [Algebra.Smooth k R]
    (q : R →ₐ[k] Q) (hq : Function.Surjective q) (z : R)
    (hker : RingHom.ker q.toRingHom = Ideal.span {z})
    (D : Derivation k R R) (hDz : D z = 1)
    {β : Type v} [Fintype β] (w : β → R) (K : Ideal Q) (F : Finset β)
    (hK : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k Q K (fun j => q (w j)) F) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R (K.comap q.toRingHom) w F := by
  intro p hp
  have hqp : RingHom.ker q.toRingHom ≤ p.asIdeal := (Ideal.comap_mono bot_le).trans hp
  let P : PrimeSpectrum Q := ⟨p.asIdeal.map q.toRingHom, Ideal.map_isPrime_of_surjective hq hqp⟩
  have hP : PrimeSpectrum.comap q.toRingHom P = p := by
    apply PrimeSpectrum.ext
    change (p.asIdeal.map q.toRingHom).comap q.toRingHom = p.asIdeal
    rw [Ideal.comap_map_of_surjective q.toRingHom hq, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hqp]
  have hKP : K ≤ P.asIdeal := by
    change K ≤ p.asIdeal.map q.toRingHom
    rw [← Ideal.map_comap_of_surjective q.toRingHom hq K]
    exact Ideal.map_mono hp
  obtain ⟨C⟩ := hK P hKP
  exact Quotient.MixedBoundaryCenterLift.Construction.quotient_mixed_boundary_center_chart_lifts R Q q hq z hker D hDz w K F p P hP C

end

end OAI.AlgebraicGeometry.Resolution.Blowups
