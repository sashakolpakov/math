import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.TransverseCoordinateFiber
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.EquationCongruence
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OpenChartComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ChartEtaleBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.QuotientPrincipalOpenEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalOpenFactorization

/-! # Component Fiber -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Removing one boundary label and restricting to that component gives an actual boundary atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.componentFiber
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] {β : Type v}
    {w : Option β → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R (Option β) w) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (R ⧸ Ideal.span {w none}))
      (fun j => Ideal.Quotient.mk (Ideal.span {w none}) (w (some j))) := by
  cases hc : M.coordinate none with
  | none =>
      have hspan : Ideal.span {w none} = ⊤ := by simpa only [hc] using M.component_ideal none
      intro p
      have h1 : Ideal.Quotient.mk (Ideal.span {w none}) (1 : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hspan]; trivial)
      have h10 : (1 : R ⧸ Ideal.span {w none}) = 0 := by simpa only [map_one] using h1
      exact False.elim (p.isPrime.one_notMem (h10.symm ▸ p.asIdeal.zero_mem))
  | some h =>
      let N := M.reindex (⟨some, Option.some_injective β⟩ : β ↪ Option β)
      have hh : ∀ j, N.coordinate j ≠ some h := by
        intro j hj
        have he := M.distinct (some j) none h hj hc
        cases he
      have hspan : Ideal.span {w none} = Ideal.span {M.map (MvPolynomial.X h)} := by
        simpa only [hc] using M.component_ideal none
      have he := congrArg (fun I : Ideal R => LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (R ⧸ I))
        (fun j => Ideal.Quotient.mk I (w (some j)))) hspan
      exact he.mpr (N.transverseCoordinateFiber h hh).hasEtaleBoundaryCharts

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.componentFiber
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R] {β : Type v}
    {w : Option β → R} (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (R ⧸ Ideal.span {w none}))
      (fun j => Ideal.Quotient.mk (Ideal.span {w none}) (w (some j))) := by
  intro pQ
  let Q := R ⧸ Ideal.span {w none}
  let q : R →ₐ[k] Q := Ideal.Quotient.mkₐ k _
  let p := PrimeSpectrum.comap q.toRingHom pQ
  obtain ⟨C⟩ := hboundary p
  obtain ⟨r, hr, g, hg, hgf⟩ := PrincipalOpenFactorization.Construction.exists_pointed_principal_open_factorization R C.carrier
    C.map p C.point C.point_over
  let A := Localization.Away r
  let f : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) := hg
  have hge : g.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom g.toRingHom)).mp inferInstance
  let M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k A (Option β) (fun j => f (w j)) :=
    (C.model.baseChange g hge).congrEquations (fun j => f (w j))
      (fun j => (AlgHom.congr_fun hgf (w j)).symm)
  let H := A ⧸ Ideal.span {algebraMap R A (w none)}
  let T := Localization.Away (Ideal.Quotient.mk (Ideal.span {w none}) r)
  let e : H ≃ₐ[k] T := QuotientPrincipalOpenEquiv.Construction.normalQuotientPrincipalOpenEquiv k (w none) r
  let a : Q →ₐ[k] T := IsScalarTower.toAlgHom k Q T
  have hH : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of H)
      (fun j => Ideal.Quotient.mk (Ideal.span {algebraMap R A (w none)}) (f (w (some j)))) := M.componentFiber
  have he : e.toAlgHom.toRingHom.Etale := RingHom.Etale.of_bijective e.bijective
  have hT : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of T) (fun j => a (q (w (some j)))) := by
    have h := hH.etale_baseChange (S := .of T) e.toAlgHom he
    convert h using 1
    funext j
    exact ((QuotientPrincipalOpenEquiv.Construction.normalQuotientPrincipalOpenEquiv_mk k (w none) r (f (w (some j)))).trans
      (Blowups.Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_constants q r (w (some j)))).symm
  have hrQ : Ideal.Quotient.mk (Ideal.span {w none}) r ∉ pQ.asIdeal := hr
  obtain ⟨P, hP⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime _ pQ hrQ
  obtain ⟨B⟩ := hT P
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom a.toRingHom)) :=
    IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk (Ideal.span {w none}) r)
  exact ⟨B.comp a (fun j => q (w (some j))) (fun _ => rfl) pQ hP⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
