import OAI.AlgebraicTopology.Duality.Poincare.RelativeCapHomologyNaturality
import OAI.AlgebraicTopology.Duality.Poincare.CompactMeaning
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace

/-! # Cap Relative Trace -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CapRelativeTrace

noncomputable section

/-!
# Ordinary cap products and relative traces

The relative cochain complex for the empty subspace is canonically the
ordinary cochain complex. Under this identification, the two-support cap
with empty cochain support gives the ordinary action on relative homology.
Projecting an ordinary mixed cap gives exactly this relative cap action.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section EmptyCochains

variable {R : Type} [Ring R]

/-- The genuine kernel defining cochains relative to the empty subspace
is canonically the ordinary singular cochain complex. -/
def relativeEmptyCochainsIso (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains M X ∅ ≅ Cohomology.Singular.Basic.singularCochains M X := by
  let : IsIso (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X ∅) :=
    kernel.ι_of_zero (CompactSupportCohomology.subspaceCochainRestriction_eq_zero_of_isEmpty M X ∅)
  exact asIso (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X ∅)

@[simp]
theorem relativeEmptyCochainsIso_hom (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    (relativeEmptyCochainsIso M X).hom = Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X ∅ := rfl

/-- The induced canonical identification of relative-empty cohomology
with ordinary singular cohomology. -/
def relativeEmptyCohomologyIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X ∅ n ≅ Cohomology.Singular.Basic.singularCohomology M X n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (relativeEmptyCochainsIso M X)

@[simp]
theorem relativeEmptyCohomologyIso_hom (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    (relativeEmptyCohomologyIso M X n).hom = Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X ∅ n := rfl

/-- The canonical relative-empty lift forgets back to the given class. -/
@[simp]
theorem relativeEmptyCohomologyIso_inv_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (a : Cohomology.Singular.Basic.singularCohomology M X n) :
    Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X ∅ n ((relativeEmptyCohomologyIso M X n).inv a) = a :=
  ConcreteCategory.congr_hom (relativeEmptyCohomologyIso M X n).inv_hom_id a

/-- The relative-empty lift commutes with ordinary pullback along the
given continuous map. -/
@[reassoc]
theorem relativeEmptyCohomologyIso_inv_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    Cohomology.Singular.Functor.singularCohomologyPullback M f n ≫ (relativeEmptyCohomologyIso M X n).inv =
      (relativeEmptyCohomologyIso M Y n).inv ≫
        Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f (Set.mapsTo_empty f ∅) n := by
  have hn :
      Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f (Set.mapsTo_empty f ∅) n ≫
          (relativeEmptyCohomologyIso M X n).hom =
        (relativeEmptyCohomologyIso M Y n).hom ≫ Cohomology.Singular.Functor.singularCohomologyPullback M f n := by
    change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
      HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      relativeEmptyCochainsIso_hom, relativeEmptyCochainsIso_hom,
      Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality]
  apply (cancel_mono (relativeEmptyCohomologyIso M X n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hn,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end EmptyCochains

/-- Projecting an ordinary input cycle to the union-relative group and
then taking the two-support cap equals projecting the ordinary mixed cap. -/
theorem twoSupportRelativeCapHomology_projection
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q)) :
    SupportRelativeCapHomology.twoSupportRelativeCapHomology X A B hA hB p q c
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (A ∪ B)) (p + q) z) =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B) q
        (MixedCapHomology.mixedSingularCapHomology X p q
          (Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A p c) z) := by
  have hp := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyMap_comp (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A)
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.subset_union_left : A ⊆ A ∪ B)) (p + q)) z
  rw [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap_projection] at hp
  simp only [ConcreteCategory.comp_apply] at hp
  rw [hp, SupportRelativeCapHomology.twoSupportRelativeCapHomology_left, CompactMeaning.relativeCapHomology_projection]

/-- The actual action of ordinary rational cohomology on relative integral
homology, obtained from the two-support cap with empty cochain support. -/
def ordinaryRelativeCapHomology (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p →ₗ[ℚ]
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B (p + q) →ₗ[ℤ] AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X B q) where
  toFun a := (SupportRelativeCapHomology.twoSupportRelativeCapHomology X ∅ B isOpen_empty hB p q
      ((relativeEmptyCohomologyIso (ModuleCat.of ℚ ℚ) X p).inv a)).comp
    (HomologicalComplex.homologyMap
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.subset_union_right : B ⊆ ∅ ∪ B)) (p + q)).hom
  map_add' a b := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' r a := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

theorem ordinaryRelativeCapHomology_apply
    (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B (p + q)) :
    ordinaryRelativeCapHomology X B hB p q a z =
      SupportRelativeCapHomology.twoSupportRelativeCapHomology X ∅ B isOpen_empty hB p q
        ((relativeEmptyCohomologyIso (ModuleCat.of ℚ ℚ) X p).inv a)
        (HomologicalComplex.homologyMap
          (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.subset_union_right : B ⊆ ∅ ∪ B)) (p + q) z) := rfl

/-- Projecting the ordinary mixed cap is exactly the ordinary relative
cap applied to the genuine projection of the integral input class. -/
theorem mixedSingularCapHomology_relativeProjection
    (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q)) :
    HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B) q
        (MixedCapHomology.mixedSingularCapHomology X p q a z) =
      ordinaryRelativeCapHomology X B hB p q a
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X B) (p + q) z) := by
  have hp := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyMap_comp (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X B)
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.subset_union_right : B ⊆ ∅ ∪ B)) (p + q)) z
  rw [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap_projection] at hp
  simp only [ConcreteCategory.comp_apply] at hp
  rw [ordinaryRelativeCapHomology_apply, ← hp, twoSupportRelativeCapHomology_projection,
    relativeEmptyCohomologyIso_inv_inclusion]

/-- The ordinary action on relative homology commutes with actual maps
of pairs, through ordinary pullback on its cohomology input. -/
theorem ordinaryRelativeCapHomology_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {B : Set X} {B' : Set Y}
    (hf : Set.MapsTo f B B') (hB : IsOpen B) (hB' : IsOpen B') (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B (p + q)) :
    HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf) q
        (ordinaryRelativeCapHomology X B hB p q
          (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f p a) z) =
      ordinaryRelativeCapHomology Y B' hB' p q a
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hf (p + q) z) := by
  have hc := ConcreteCategory.congr_hom
    (relativeEmptyCohomologyIso_inv_naturality (ModuleCat.of ℚ ℚ) f p) a
  simp only [ConcreteCategory.comp_apply] at hc
  rw [ordinaryRelativeCapHomology_apply, ordinaryRelativeCapHomology_apply, hc,
    RelativeCapHomologyNaturality.twoSupportRelativeCapHomology_naturality f (Set.mapsTo_empty f ∅) hf
      isOpen_empty hB isOpen_empty hB']
  apply congrArg (SupportRelativeCapHomology.twoSupportRelativeCapHomology Y ∅ B' isOpen_empty hB' p q
    ((relativeEmptyCohomologyIso (ModuleCat.of ℚ ℚ) Y p).inv a))
  have hm :
      HomologicalComplex.homologyMap
          (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.subset_union_right : B ⊆ ∅ ∪ B)) (p + q) ≫
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f
          ((Set.mapsTo_empty f ∅).union_union hf) (p + q) =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hf (p + q) ≫
        HomologicalComplex.homologyMap
          (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap Y (Set.subset_union_right : B' ⊆ ∅ ∪ B')) (p + q) := by
    change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    dsimp only [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap]
    rw [AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap_comp, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  exact ConcreteCategory.congr_hom hm z

/-- The ordinary relative cap action commutes with the genuine integral
and rational excision isomorphisms around a compact support. -/
theorem ordinaryRelativeCapHomology_excision
    (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of U)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) (p + q)) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles.rationalCompactSupportExcisionHomologyIso X U K hK hU hKU q).hom
        (ordinaryRelativeCapHomology (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ)
          (hK.isClosed.isOpen_compl.preimage (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U).hom.continuous) p q
          (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) p a) z) =
      ordinaryRelativeCapHomology X Kᶜ hK.isClosed.isOpen_compl p q a
        ((AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X U K hK hU hKU (p + q)).hom z) := by
  rw [AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles.rationalCompactSupportExcisionHomologyIso_hom,
    AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso_hom]
  exact ordinaryRelativeCapHomology_naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ hx => hx)
    (hK.isClosed.isOpen_compl.preimage (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U).hom.continuous)
    hK.isClosed.isOpen_compl p q a z

/-- Tracing an ordinary mixed cap to a compact support in an open subspace
is the genuine relative cap in that subspace, with its integral input
obtained by projection and the proved inverse excision map. -/
theorem compactRelativeTrace_mixedSingularCapHomology
    (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles.compactRelativeTrace X U K hK hU hKU q (MixedCapHomology.mixedSingularCapHomology X p q a z) =
      ordinaryRelativeCapHomology (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ)
        (hK.isClosed.isOpen_compl.preimage (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U).hom.continuous) p q
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) p a)
        ((AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X U K hK hU hKU (p + q)).inv
          (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ) (p + q) z)) := by
  apply (ModuleCat.mono_iff_injective
    (AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles.rationalCompactSupportExcisionHomologyIso X U K hK hU hKU q).hom).mp inferInstance
  have ht := ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles.compactRelativeTrace_excision X U K hK hU hKU q)
    (MixedCapHomology.mixedSingularCapHomology X p q a z)
  have hz := ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X U K hK hU hKU (p + q)).inv_hom_id
    (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ) (p + q) z)
  simp only [ConcreteCategory.comp_apply] at ht hz
  rw [ht, ordinaryRelativeCapHomology_excision, hz]
  exact mixedSingularCapHomology_relativeProjection X Kᶜ hK.isClosed.isOpen_compl p q a z

end

end OAI.AlgebraicTopology.Duality.Poincare.CapRelativeTrace
