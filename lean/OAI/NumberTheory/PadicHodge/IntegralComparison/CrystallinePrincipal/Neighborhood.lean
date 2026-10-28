import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Continuous

/-! # Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Neighborhood

noncomputable section

/-!
# IntegralComparison: principal neighborhoods for crystalline pullbacks

An ambient point mapping into a principal open has a principal
neighborhood in the original thickening on which the target function
is a unit. This works for every crystalline morphism in the slice.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category (Principal)
open OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

theorem unit_of_all_points {R : Type u} [CommRing R] (t : R)
    (ht : ∀ z : PrimeSpectrum R, z ∈ PrimeSpectrum.basicOpen t) : IsUnit t := by
  by_contra h
  obtain ⟨I, hI, hi⟩ := exists_max_ideal_of_mem_nonunits h
  exact ht ⟨I, hI.isPrime⟩ hi

theorem neighborhood {r : PrincipalOpens.Category.Principal U.ring} {V : BigCrystallineSite.Object p B J δ f}
    (β : ((Functor.inclusion U).obj r).left ⟶ V) (t : V.ring)
    (w : Spec ((Functor.inclusion U).obj r).left.ring)
    (hw : BigCrystallineSite.Object.ambient.map β w ∈ PrimeSpectrum.basicOpen t) :
    ∃ (s : PrincipalOpens.Category.Principal U.ring) (a : s ⟶ r),
      BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom U r.function) w ∈ PrimeSpectrum.basicOpen s.function ∧
      IsUnit ((((Functor.inclusion U).map a).left ≫ β).ringMap t) := by
  let j : Spec ((Functor.inclusion U).obj r).left.ring ⟶ Spec U.ring :=
    BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom U r.function)
  let b : Spec ((Functor.inclusion U).obj r).left.ring ⟶ Spec V.ring := BigCrystallineSite.Object.ambient.map β
  have : IsOpenImmersion j := Crystalline.Localization.hom_open U r.function
  let O : Set (PrimeSpectrum U.ring) :=
    j '' (b ⁻¹' (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum V.ring)))
  have hO : IsOpen O := j.isOpenEmbedding.isOpenMap _
    ((PrimeSpectrum.basicOpen t).isOpen.preimage b.continuous)
  have hwO : j w ∈ O := ⟨w, hw, rfl⟩
  obtain ⟨_, ⟨s, rfl⟩, hs, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hwO hO
  have hsr : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r.function := by
    intro z hz
    obtain ⟨v, _, hv⟩ := hsub hz
    rw [← Crystalline.Localization.hom_range U r.function]
    exact ⟨v, hv⟩
  let a : PrincipalOpens.Category.Principal.mk s ⟶ r := homOfLE hsr
  refine ⟨⟨s⟩, a, hs, unit_of_all_points _ ?_⟩
  intro z
  have hz : BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom U s) z ∈ PrimeSpectrum.basicOpen s := by
    rw [← Crystalline.Localization.hom_range U s]
    exact ⟨z, rfl⟩
  obtain ⟨v, hv, he⟩ := hsub hz
  have he' : v = BigCrystallineSite.Object.ambient.map ((Functor.inclusion U).map a).left z := by
    apply j.isOpenEmbedding.injective
    have h := congrArg (fun g => BigCrystallineSite.Object.ambient.map g) (Over.w ((Functor.inclusion U).map a))
    rw [BigCrystallineSite.Object.ambient.map_comp] at h
    have hz' : j (BigCrystallineSite.Object.ambient.map ((Functor.inclusion U).map a).left z) =
        BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom U s) z := congrArg (fun g => g z) h
    exact he.trans hz'.symm
  rw [he'] at hv
  exact hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Neighborhood
