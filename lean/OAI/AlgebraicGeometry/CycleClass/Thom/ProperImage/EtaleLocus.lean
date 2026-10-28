import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.FunctionFields
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Field

/-! # Etale Locus -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleLocus.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem formallyEtale_respectsIso : RingHom.RespectsIso @RingHom.FormallyEtale := by
  have hc : RingHom.StableUnderComposition @RingHom.FormallyEtale :=
    fun _ _ _ _ _ _ _ _ hf hg => hf.comp hg
  apply hc.respectsIso
  intro R S _ _ e
  let := e.toRingHom.toAlgebra
  let : Algebra.Etale R S := RingHom.Etale.of_bijective e.bijective
  exact inferInstanceAs (Algebra.FormallyEtale R S)

theorem formallyEtale_stalkMap_iff {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyEtale ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.etaleLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyEtale_algebraMap]
    exact formallyEtale_respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Algebra.FormallyEtale.iff_restrictScalars.symm

/-- Formal etaleness at a stalk spreads to a genuine affine etale
neighborhood for a morphism locally of finite presentation. -/
theorem exists_etale_of_formallyEtale_stalk {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ U), x ∈ V ∧ (f.appLE U V hVU).hom.Etale := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsEtaleAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (formallyEtale_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · have hm : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hrx
    change hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ X.basicOpen r at hm
    simpa only [hV.fromSpec_primeIdealOf] using hm
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.etale_algebraMap] at hr
    convert!
      RingHom.Etale.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _)]
    rw [AlgEquiv.commutes]
    exact congrArg (fun k : Γ(Y, U) ⟶ Γ(X, X.basicOpen r) => k _)
      (f.appLE_map hVU (homOfLE (X.basicOpen_le r)).op).symm

theorem exists_etale_neighborhood {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ (U : Y.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U),
      x ∈ V ∧ Etale (f.resLE U V hVU) := by
  obtain ⟨U, hU, V, hV, hVU, hxV, he⟩ := exists_etale_of_formallyEtale_stalk f x H
  refine ⟨U, V, hVU, hxV, ?_⟩
  let : IsAffine U := hU
  let : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  exact (RingHom.Etale.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr he

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleLocus.Constructions.Construction
