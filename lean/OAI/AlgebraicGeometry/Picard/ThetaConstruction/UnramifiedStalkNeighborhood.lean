import OAI.AlgebraicGeometry.Cycles.Functoriality.EtaleLocus
import Mathlib.RingTheory.Unramified.Locus

/-! # Unramified Stalk Neighborhood -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.UnramifiedStalkNeighborhood.Geometric

noncomputable section

/-! Formal unramifiedness of an actual stalk map spreads to an
original open source neighborhood for a locally finite-type morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem formallyUnramified_stalkMap_iff {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyUnramified ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.unramifiedLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let : q.LiesOver p :=
    ⟨congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyUnramified_algebraMap]
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · constructor
    · intro h
      let := h
      exact Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p) (Localization.AtPrime q)
    · intro h
      let : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime q) := h
      exact Algebra.FormallyUnramified.of_restrictScalars Γ(Y, U)
        (Localization.AtPrime p) (Localization.AtPrime q)

theorem exists_unramified_of_stalk {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (H : (f.stalkMap x).hom.FormallyUnramified) :
    ∃ V : X.Opens, x ∈ V ∧ FormallyUnramified (V.ι ≫ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have hf := f.finiteType_appLE hU hV hVU
  let := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra.FiniteType Γ(Y, U) Γ(X, V) := hf
  let : Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (formallyUnramified_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt
    (R := Γ(Y, U)) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let W := X.basicOpen r
  have hW := hV.basicOpen r
  have hWU : W ≤ f ⁻¹ᵁ U := (X.basicOpen_le r).trans hVU
  have hxW : x ∈ W := by
    have hm : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ W := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hrx
    change hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ W at hm
    simpa only [hV.fromSpec_primeIdealOf] using hm
  have hw : (f.appLE U W hWU).hom.FormallyUnramified := by
    let := hV.isLocalization_basicOpen r
    rw [← RingHom.formallyUnramified_algebraMap] at hr
    convert! RingHom.FormallyUnramified.propertyIsLocal.respectsIso.1 _
      (IsLocalization.algEquiv (.powers r) _ Γ(X, W)).toRingEquiv hr using 1
    ext a
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _)]
    rw [AlgEquiv.commutes]
    exact congrArg (fun k : Γ(Y, U) ⟶ Γ(X, W) => k a)
      (f.appLE_map hVU (homOfLE (X.basicOpen_le r)).op).symm
  let : IsAffine U := hU
  let : IsAffine W := hW
  let : FormallyUnramified (f.resLE U W hWU) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)]
    exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U W hWU)).mpr hw
  refine ⟨W, hxW, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f hWU]
  exact MorphismProperty.comp_mem (@FormallyUnramified) _ _
    inferInstance inferInstance

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.UnramifiedStalkNeighborhood.Geometric
