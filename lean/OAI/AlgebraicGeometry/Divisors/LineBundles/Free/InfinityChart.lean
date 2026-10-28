import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveInfinityChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleLocalBasis
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Localization
import Mathlib.RingTheory.Localization.Module

/-! # Infinity Chart -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles.Free.InfinityChart.BundleCycles

/-! Principal module trivializations supply actual finite free
infinity charts for every finite projective augmented bundle. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]

theorem projectiveModule_hasFreeInfinityCharts :
    ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))
      (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M) := by
  intro x
  let : x.asIdeal.IsPrime := x.isPrime
  obtain ⟨a, ha, κ, hκ, ⟨basis⟩⟩ := LineBundles.Projective.ModuleLocalBasis.BundleCycles.projectiveModule_exists_localBasis M x.asIdeal
  let := hκ
  let := Fintype.ofFinite κ
  let S := Localization.Away a
  let N := LocalizedModule.Away a M
  let m : M →ₗ[R] N := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let am : R × M →ₗ[R] S × N := Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap (S := S) m
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let j := SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers a) am
  refine ⟨{
    coefficient := .of S
    module := ModuleCat.of S N
    rank := Fintype.card κ
    basis := basis.reindex (Fintype.equivFin κ)
    baseMap := i
    totalMap := j
    open_base := IsOpenImmersion.of_isLocalization a
    open_total := SymmetricProjective.PrincipalOpen.BundleCycles.localizedSymmetricProjectiveMap_isOpenImmersion (S := S) a am
    contains := ?_
    square := Augmented.ModuleLocalization.BundleCycles.symmetricAugmentedProjective_principal_isPullback (S := S) a m
    idealIso := SymmetricInfinity.Localization.BundleCycles.symmetricInfinity_localization_idealIso a m }⟩
  have he : Set.range i = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range S a
  exact he.symm ▸ ha

end AlgebraicGeometry.Divisors.LineBundles.Free.InfinityChart.BundleCycles

namespace AlgebraicGeometry.Divisors.LineBundles.Free
open _root_.AlgebraicGeometry
open _root_.CategoryTheory
section

/-! Principal localization refines an actual finite free infinity chart
without changing its rank or the identified Cartier ideal. -/

variable {E X : Scheme.{0}} {p : E ⟶ X} {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E} {x : X}
    (C : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L x) (a : C.coefficient)

def ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart.localize
    (u : Spec (.of (Localization.Away a))) :
    ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L
      ((Spec.map (CommRingCat.ofHom (algebraMap C.coefficient (Localization.Away a))) ≫ C.baseMap) u) := by
  let R := C.coefficient
  let M := C.module
  let S := Localization.Away a
  let N := LocalizedModule.Away a M
  let m : M →ₗ[R] N := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let am : R × M →ₗ[R] S × N := Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap (S := S) m
  let i : Spec (.of S) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let j := SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers a) am
  let D : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))
      (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M) (i u) := {
    coefficient := .of S
    module := ModuleCat.of S N
    rank := C.rank
    basis := C.basis.ofIsLocalizedModule S (Submonoid.powers a) m
    baseMap := i
    totalMap := j
    open_base := IsOpenImmersion.of_isLocalization a
    open_total := SymmetricProjective.PrincipalOpen.BundleCycles.localizedSymmetricProjectiveMap_isOpenImmersion (S := S) a am
    contains := ⟨u, rfl⟩
    square := Augmented.ModuleLocalization.BundleCycles.symmetricAugmentedProjective_principal_isPullback (S := S) a m
    idealIso := SymmetricInfinity.Localization.BundleCycles.symmetricInfinity_localization_idealIso a m }
  exact D.compOpen p C.baseMap C.totalMap C.square L C.idealIso

theorem ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart.localize_rank (u : Spec (.of (Localization.Away a))) :
    (C.localize a u).rank = C.rank := rfl

theorem ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart.localize_baseMap (u : Spec (.of (Localization.Away a))) :
    (C.localize a u).baseMap =
      Spec.map (CommRingCat.ofHom (algebraMap C.coefficient (Localization.Away a))) ≫ C.baseMap := rfl

end

/-! Actual infinity charts can be refined inside any open neighborhood
of their chosen base point, preserving the free rank. -/

theorem ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart.refineOpen {E X : Scheme.{0}}
    {p : E ⟶ X} {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E} {x : X} (C : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L x)
    (W : X.Opens) (hx : x ∈ W) :
    ∃ D : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L x, D.rank = C.rank ∧ Set.range D.baseMap ⊆ W := by
  obtain ⟨u, hu⟩ := C.contains
  let V := C.baseMap ⁻¹ᵁ W
  have huV : u ∈ V := by
    change C.baseMap u ∈ W
    rw [hu]
    exact hx
  obtain ⟨_, ⟨a, rfl⟩, hua, haV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp V.isOpen u huV
  let i : Spec (.of (Localization.Away a)) ⟶ Spec C.coefficient :=
    Spec.map (CommRingCat.ofHom (algebraMap C.coefficient (Localization.Away a)))
  have he : Set.range i = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum C.coefficient)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  have huRange : u ∈ Set.range i := by
    rw [he]
    exact hua
  obtain ⟨v, hv⟩ := huRange
  have hy : (i ≫ C.baseMap) v = x := (congrArg C.baseMap hv).trans hu
  have H : ∃ D : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L ((i ≫ C.baseMap) v),
      D.rank = C.rank ∧ Set.range D.baseMap ⊆ W := by
    refine ⟨C.localize a v, rfl, ?_⟩
    rintro y ⟨w, rfl⟩
    apply haV
    change i w ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum C.coefficient))
    rw [← he]
    exact ⟨w, rfl⟩
  exact (congrArg (fun y : X => ∃ D : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L y,
    D.rank = C.rank ∧ Set.range D.baseMap ⊆ W) hy).mp H

end AlgebraicGeometry.Divisors.LineBundles.Free

end

end OAI
