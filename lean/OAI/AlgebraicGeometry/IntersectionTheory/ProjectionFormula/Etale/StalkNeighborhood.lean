import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.EqualDimensionEtale
import Mathlib.RingTheory.Etale.Locus
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Stalk Neighborhood -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.StalkNeighborhood

noncomputable section

/-! Formal etaleness of a stalk of a finitely presented morphism
extends to an actual affine etale neighborhood. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ringHom_iff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.FormallyEtale ↔ f.FormallyUnramified ∧ f.FormallySmooth := by
  let := f.toAlgebra
  exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth

theorem stalk_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyEtale ↔
      Algebra.IsEtaleAt Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyEtale_algebraMap, ringHom_iff, ringHom_iff]
    exact and_congr
      (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
        (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx))
      (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
        (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx))
  · exact Algebra.FormallyEtale.iff_restrictScalars.symm

theorem exists_affine {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U),
      x ∈ V ∧ (f.appLE U V hVU).hom.Etale := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsEtaleAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (stalk_iff f x U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, U)) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.etale_algebraMap] at hr
    convert! RingHom.Etale.propertyIsLocal.respectsIso.1 _
      (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext c
    dsimp
    rw [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      (IsLocalization.algEquiv (.powers r) (Localization.Away r) Γ(X, X.basicOpen r)).commutes]
    change (f.appLE U (X.basicOpen r) _) c =
      (f.appLE U V hVU ≫ X.presheaf.map (homOfLE (X.basicOpen_le r)).op) c
    rw [Scheme.Hom.appLE_map]

theorem exists_open {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hVU, hx, Hφ⟩ := exists_affine f x H
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have hres : Etale (f.resLE U V hVU) := by
    apply (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mpr
    change RingHom.Etale ((f.resLE U V hVU).app ⊤).hom
    rw [Scheme.Hom.resLE_app_top]
    exact ((RingHom.Etale.respectsIso.cancel_left_isIso U.topIso.hom
      (f.appLE U V hVU ≫ V.topIso.inv)).trans
      (RingHom.Etale.respectsIso.cancel_right_isIso (f.appLE U V hVU) V.topIso.inv)).mpr Hφ
  let := hres
  refine ⟨V, hx, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f hVU]
  infer_instance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.StalkNeighborhood
