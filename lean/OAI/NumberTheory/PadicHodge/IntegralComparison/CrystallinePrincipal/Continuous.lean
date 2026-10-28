import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Limits
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Topology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology
import Mathlib.CategoryTheory.Sites.Over

/-! # Continuous -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Continuous

noncomputable section

/-!
# IntegralComparison: continuity of principal opens in a crystalline slice

The maps of principal opens are actual cartesian crystalline open
immersions. Point-covering sieves therefore give covering families in
the original crystalline topology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category (Principal)
open OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

instance hom_closed_open (r : U.ring) : IsOpenImmersion (BigCrystallineSite.Object.closed.map (Crystalline.Localization.hom U r)) :=
  MorphismProperty.of_isPullback (Crystalline.Localization.hom_cartesian U r).flip (Crystalline.Localization.hom_open U r)

instance map_ambient_open {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s) :
    IsOpenImmersion (BigCrystallineSite.Object.ambient.map ((CrystallinePrincipal.Functor.inclusion U).map a).left) := by
  have he := congrArg (fun g => BigCrystallineSite.Object.ambient.map g) (Over.w ((CrystallinePrincipal.Functor.inclusion U).map a))
  rw [BigCrystallineSite.Object.ambient.map_comp] at he
  have ho : IsOpenImmersion (BigCrystallineSite.Object.ambient.map ((CrystallinePrincipal.Functor.inclusion U).obj r).hom) := Crystalline.Localization.hom_open U r.function
  have : IsOpenImmersion (BigCrystallineSite.Object.ambient.map ((CrystallinePrincipal.Functor.inclusion U).obj s).hom) := Crystalline.Localization.hom_open U s.function
  have : IsOpenImmersion
      (BigCrystallineSite.Object.ambient.map ((CrystallinePrincipal.Functor.inclusion U).map a).left ≫ BigCrystallineSite.Object.ambient.map ((CrystallinePrincipal.Functor.inclusion U).obj s).hom) :=
    he.symm ▸ ho
  exact IsOpenImmersion.of_comp _ (BigCrystallineSite.Object.ambient.map ((CrystallinePrincipal.Functor.inclusion U).obj s).hom)

instance map_closed_open {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s) :
    IsOpenImmersion (BigCrystallineSite.Object.closed.map ((CrystallinePrincipal.Functor.inclusion U).map a).left) := by
  have he := congrArg (fun g => BigCrystallineSite.Object.closed.map g) (Over.w ((CrystallinePrincipal.Functor.inclusion U).map a))
  rw [BigCrystallineSite.Object.closed.map_comp] at he
  have ho : IsOpenImmersion (BigCrystallineSite.Object.closed.map ((CrystallinePrincipal.Functor.inclusion U).obj r).hom) := hom_closed_open U r.function
  have : IsOpenImmersion (BigCrystallineSite.Object.closed.map ((CrystallinePrincipal.Functor.inclusion U).obj s).hom) := hom_closed_open U s.function
  have : IsOpenImmersion
      (BigCrystallineSite.Object.closed.map ((CrystallinePrincipal.Functor.inclusion U).map a).left ≫ BigCrystallineSite.Object.closed.map ((CrystallinePrincipal.Functor.inclusion U).obj s).hom) :=
    he.symm ▸ ho
  exact IsOpenImmersion.of_comp _ (BigCrystallineSite.Object.closed.map ((CrystallinePrincipal.Functor.inclusion U).obj s).hom)

theorem map_cartesian {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s) :
    BigCrystallineSite.Object.Cartesian ((CrystallinePrincipal.Functor.inclusion U).map a).left := by
  have : IsClosedImmersion (BigCrystallineSite.Object.closedImmersion.app ((CrystallinePrincipal.Functor.inclusion U).obj s).left) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact Crystalline.Cartesian.isPullback_of_open_closed_surjective _ _ _ _
    (BigCrystallineSite.Object.closedImmersion.naturality ((CrystallinePrincipal.Functor.inclusion U).map a).left)
    (Crystalline.ClosedTopology.quotientSpec_surjective _)

theorem image_covering {r : PrincipalOpens.Category.Principal U.ring} (S : Sieve r)
    (hS : S ∈ Principal.Topology.topology U.ring r) :
    (S.arrows.map (CrystallinePrincipal.Functor.inclusion U)).map (Over.forget U) ∈ BigCrystallineSite.Object.precoverage _ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro y
    have hy : BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom U r.function) y ∈ PrimeSpectrum.basicOpen r.function := by
      rw [← Crystalline.Localization.hom_range U r.function]
      exact ⟨y, rfl⟩
    obtain ⟨s, a, ha, hs⟩ := (Principal.Topology.covering_iff U.ring S).mp hS _ hy
    rw [← Crystalline.Localization.hom_range U s.function] at hs
    obtain ⟨z, hz⟩ := hs
    refine ⟨_, Scheme.forget.map (BigCrystallineSite.Object.ambient.map ((Over.forget U).map ((CrystallinePrincipal.Functor.inclusion U).map a))),
      ?_, z, ?_⟩
    · exact Presieve.map.of (Presieve.map.of (Presieve.map.of (Presieve.map.of ha)))
    ·
      apply (BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom U r.function)).isOpenEmbedding.injective
      change (BigCrystallineSite.Object.ambient.map ((CrystallinePrincipal.Functor.inclusion U).map a).left ≫
        BigCrystallineSite.Object.ambient.map ((CrystallinePrincipal.Functor.inclusion U).obj r).hom) z = _
      rw [← BigCrystallineSite.Object.ambient.map_comp, Over.w]
      exact hz
  · intro V a ha
    cases ha with
    | of ha => cases ha with
      | of ha => cases ha with
        | of ha =>
          rename_i s a
          exact map_ambient_open U a
  · intro V a ha
    cases ha with
    | of ha => cases ha with
      | of ha =>
        rename_i s a
        exact map_cartesian U a

theorem inclusion_coverPreserving : CoverPreserving (Principal.Topology.topology U.ring)
    (BigCrystallineSite.Object.topology.over U) (CrystallinePrincipal.Functor.inclusion U) where
  cover_preserve {r S} hS := by
    rw [GrothendieckTopology.mem_over_iff]
    apply BigCrystallineSite.Object.topology.superset_covering ?_
      (BigCrystallineSite.Object.precoverage.generate_mem_toGrothendieck (image_covering U S hS))
    apply (Sieve.generate_le_iff _ _).mpr
    intro V a ha
    cases ha with
    | of ha => cases ha with
      | of ha =>
        exact ⟨_, (CrystallinePrincipal.Functor.inclusion U).map _, 𝟙 _, ⟨_, _, 𝟙 _, ha, (Category.id_comp _).symm⟩,
          (Category.id_comp _).symm⟩

instance inclusion_continuous : (CrystallinePrincipal.Functor.inclusion U).IsContinuous
    (Principal.Topology.topology U.ring) (BigCrystallineSite.Object.topology.over U) :=
  Functor.isContinuous_iff_coverPreserving.mpr (inclusion_coverPreserving U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Continuous
