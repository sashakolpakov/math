import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction

/-! # Compact Relative Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace

noncomputable section

/-!
# Ordinary rational homology traced to a compact support in an open subspace

The trace is the actual absolute-to-relative homology projection followed
by the inverse of excision. Rational excision is obtained from the proved
integral excision isomorphism and the natural scalar-extension comparison.
Its forward map is the actual inclusion of pairs.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

/-- Rational excision around a compact support in an open neighborhood,
through the proved natural comparison with integral relative homology. -/
def rationalCompactSupportExcisionHomologyIso
    (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) n ≅
      RelativeScalarChains.Cycles.relativeScalarHomology ℚ X Kᶜ n :=
  RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) n ≪≫
    RationalScalarExtension.Cycles.rationalizeModules.mapIso (CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X U K hK hU hKU n) ≪≫
      (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X Kᶜ n).symm

/-- The forward rational excision map is the genuine relative homology
map induced by the subspace inclusion. -/
@[simp]
theorem rationalCompactSupportExcisionHomologyIso_hom
    (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    (rationalCompactSupportExcisionHomologyIso X U K hK hU hKU n).hom =
      HomologicalComplex.homologyMap
        (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (LocalHomology.Cycles.subspaceInclusion X U)
          (show Set.MapsTo (LocalHomology.Cycles.subspaceInclusion X U)
            ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) Kᶜ from fun _ hx => hx)) n := by
  dsimp only [rationalCompactSupportExcisionHomologyIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  change (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of U)
      ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) n).hom ≫
    RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap (LocalHomology.Cycles.subspaceInclusion X U)
      (fun _ hx => hx) n) ≫ (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X Kᶜ n).inv = _
  rw [← RationalRelativeHomology.Cycles.rationalRelativeHomologyIso_hom_naturality_assoc (LocalHomology.Cycles.subspaceInclusion X U)
    (A := (LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) (B := Kᶜ) (fun _ hx => hx) n,
    Iso.hom_inv_id, Category.comp_id]

/-- Trace an actual ordinary rational homology class into an open
neighborhood relative to the complement of its compact support. -/
def compactRelativeTrace (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n ⟶
      RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) n :=
  HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X Kᶜ) n ≫
    (rationalCompactSupportExcisionHomologyIso X U K hK hU hKU n).inv

/-- Including the traced class back into the ambient relative group gives
exactly the original absolute-to-relative projection. -/
@[reassoc (attr := simp)]
theorem compactRelativeTrace_excision (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    compactRelativeTrace X U K hK hU hKU n ≫
        (rationalCompactSupportExcisionHomologyIso X U K hK hU hKU n).hom =
      HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X Kᶜ) n := by
  rw [compactRelativeTrace, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Excision commutes with a genuine continuous map of the ambient and
neighborhood pairs. No properness condition is needed for ordinary chains. -/
@[reassoc]
theorem rationalCompactSupportExcisionHomologyIso_naturality
    {X Y : TopCat.{0}} [T2Space X] [T2Space Y]
    {U K : Set X} {V L : Set Y} (f : X ⟶ Y)
    (hUV : Set.MapsTo f U V) (hKL : Set.MapsTo f Kᶜ Lᶜ)
    (hK : IsCompact K) (hL : IsCompact L) (hU : IsOpen U) (hV : IsOpen V)
    (hKU : K ⊆ U) (hLV : L ⊆ V) (n : ℕ) :
    (rationalCompactSupportExcisionHomologyIso X U K hK hU hKU n).hom ≫
        HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hKL) n =
      HomologicalComplex.homologyMap
          (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (LocalHomology.Cycles.subspaceMap f hUV)
            (show Set.MapsTo (LocalHomology.Cycles.subspaceMap f hUV)
              ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) ((LocalHomology.Cycles.subspaceInclusion Y V) ⁻¹' Lᶜ)
              from fun _ hx => hKL hx)) n ≫
        (rationalCompactSupportExcisionHomologyIso Y V L hL hV hLV n).hom := by
  rw [rationalCompactSupportExcisionHomologyIso_hom,
    rationalCompactSupportExcisionHomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    RelativeScalarChains.Cycles.relativeScalarChainsMap_comp, RelativeScalarChains.Cycles.relativeScalarChainsMap_comp]
  rfl

/-- Ordinary pushforward and the compact relative trace commute for
continuous maps of the stated pairs and their open neighborhoods. -/
@[reassoc]
theorem compactRelativeTrace_naturality
    {X Y : TopCat.{0}} [T2Space X] [T2Space Y]
    {U K : Set X} {V L : Set Y} (f : X ⟶ Y)
    (hUV : Set.MapsTo f U V) (hKL : Set.MapsTo f Kᶜ Lᶜ)
    (hK : IsCompact K) (hL : IsCompact L) (hU : IsOpen U) (hV : IsOpen V)
    (hKU : K ⊆ U) (hLV : L ⊆ V) (n : ℕ) :
    HomologicalComplex.homologyMap ((RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f) n ≫
        compactRelativeTrace Y V L hL hV hLV n =
      compactRelativeTrace X U K hK hU hKU n ≫
        HomologicalComplex.homologyMap
          (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (LocalHomology.Cycles.subspaceMap f hUV)
            (show Set.MapsTo (LocalHomology.Cycles.subspaceMap f hUV)
              ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) ((LocalHomology.Cycles.subspaceInclusion Y V) ⁻¹' Lᶜ)
              from fun _ hx => hKL hx)) n := by
  apply (cancel_mono
    (rationalCompactSupportExcisionHomologyIso Y V L hL hV hLV n).hom).mp
  rw [Category.assoc, compactRelativeTrace_excision, Category.assoc,
    ← rationalCompactSupportExcisionHomologyIso_naturality
      f hUV hKL hK hL hU hV hKU hLV n,
    ← Category.assoc, compactRelativeTrace_excision,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality]

/-- Decreasing the compact support after taking the trace is the same
as tracing directly to the smaller compact support. -/
@[reassoc]
theorem compactRelativeTrace_support (X : TopCat.{0}) [T2Space X]
    (U : Set X) {K L : Set X} (hK : IsCompact K) (hL : IsCompact L)
    (hU : IsOpen U) (hKL : K ⊆ L) (hLU : L ⊆ U) (n : ℕ) :
    compactRelativeTrace X U L hL hU hLU n ≫
        HomologicalComplex.homologyMap
          (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (𝟙 (TopCat.of U))
            (show Set.MapsTo (𝟙 (TopCat.of U))
              ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Lᶜ) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ)
              from fun _ hx h => hx (hKL h))) n =
      compactRelativeTrace X U K hK hU (hKL.trans hLU) n := by
  have h := compactRelativeTrace_naturality (U := U) (V := U) (K := L) (L := K)
    (𝟙 X) (fun _ hx => hx) (fun _ hx h => hx (hKL h))
    hL hK hU hU hLU (hKL.trans hLU) n
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id, Category.id_comp] at h
  exact h.symm

/-- Including one open neighborhood of a compact support in another
carries the trace to the trace in the larger neighborhood. -/
@[reassoc]
theorem compactRelativeTrace_neighborhood (X : TopCat.{0}) [T2Space X]
    {U V K : Set X} (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V)
    (hKU : K ⊆ U) (hUV : U ⊆ V) (n : ℕ) :
    compactRelativeTrace X U K hK hU hKU n ≫
        HomologicalComplex.homologyMap
          (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (LocalHomology.Cycles.subspaceMap (𝟙 X) hUV)
            (show Set.MapsTo (LocalHomology.Cycles.subspaceMap (𝟙 X) hUV)
              ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) ((LocalHomology.Cycles.subspaceInclusion X V) ⁻¹' Kᶜ)
              from fun _ hx => hx)) n =
      compactRelativeTrace X V K hK hV (hKU.trans hUV) n := by
  have h := compactRelativeTrace_naturality (U := U) (V := V) (K := K) (L := K)
    (𝟙 X) hUV (fun _ hx => hx) hK hK hU hV hKU (hKU.trans hUV) n
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id, Category.id_comp] at h
  exact h.symm

/-- Scalar relative homology over a support restricts to the genuine
local scalar homology at each point of that support. -/
def scalarLocalHomologyToPoint (R : Type) [CommRing R]
    (X : TopCat.{0}) (K : Set X) (x : X) (hx : x ∈ K) (n : ℕ) :
    RelativeScalarChains.Cycles.relativeScalarHomology R X Kᶜ n ⟶ RelativeScalarChains.Cycles.localScalarHomology R X x n :=
  HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R (𝟙 X) (by
    intro y hy
    change y ≠ x
    intro h
    exact hy (h.symm ▸ hx))) n

/-- Projecting an ordinary scalar class and then restricting to a point
is exactly the ordinary projection to the punctured relative group. -/
@[reassoc]
theorem scalarLocalHomologyToPoint_projection (R : Type) [CommRing R]
    (X : TopCat.{0}) (K : Set X) (x : X) (hx : x ∈ K) (n : ℕ) :
    HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ) n ≫
        scalarLocalHomologyToPoint R X K x hx n =
      HomologicalComplex.homologyMap
        (RelativeScalarChains.Cycles.relativeScalarChainProjection R X ({x}ᶜ : Set X)) n := by
  unfold scalarLocalHomologyToPoint
  rw [← HomologicalComplex.homologyMap_comp, RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Actual rational local homology is unchanged by passage to an open
neighborhood. Only the usual `T1` separation hypothesis is needed here. -/
def rationalLocalExcisionHomologyIso (X : TopCat.{0}) [T1Space X]
    (U : Set X) (x : X) (hxU : x ∈ U) (hU : IsOpen U) (n : ℕ) :
    RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of U) (⟨x, hxU⟩ : U) n ≅
      RelativeScalarChains.Cycles.localScalarHomology ℚ X x n :=
  RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of U) ({(⟨x, hxU⟩ : U)}ᶜ : Set U) n ≪≫
    RationalScalarExtension.Cycles.rationalizeModules.mapIso (LocalExcision.Cycles.localExcisionHomologyIso X U x hxU hU n) ≪≫
      (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X ({x}ᶜ : Set X) n).symm

/-- Rational local excision has the actual pair-inclusion map as its
forward map, rather than merely an abstract isomorphism of modules. -/
@[simp]
theorem rationalLocalExcisionHomologyIso_hom (X : TopCat.{0}) [T1Space X]
    (U : Set X) (x : X) (hxU : x ∈ U) (hU : IsOpen U) (n : ℕ) :
    (rationalLocalExcisionHomologyIso X U x hxU hU n).hom =
      HomologicalComplex.homologyMap
        (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (LocalHomology.Cycles.subspaceInclusion X U)
          (show Set.MapsTo (LocalHomology.Cycles.subspaceInclusion X U)
            ({(⟨x, hxU⟩ : U)}ᶜ : Set U) ({x}ᶜ : Set X) from by
              intro y hy
              change y.val ≠ x
              intro h
              exact hy (Subtype.ext h))) n := by
  dsimp only [rationalLocalExcisionHomologyIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  rw [LocalExcision.Cycles.localExcisionHomologyIso_hom]
  change (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of U)
      ({(⟨x, hxU⟩ : U)}ᶜ : Set U) n).hom ≫
    RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap (LocalHomology.Cycles.subspaceInclusion X U)
      (by intro y hy; exact fun h => hy (Subtype.ext h)) n) ≫
        (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X ({x}ᶜ : Set X) n).inv = _
  rw [← RationalRelativeHomology.Cycles.rationalRelativeHomologyIso_hom_naturality_assoc (LocalHomology.Cycles.subspaceInclusion X U)
    (A := ({(⟨x, hxU⟩ : U)}ᶜ : Set U)) (B := ({x}ᶜ : Set X))
    (by intro y hy; exact fun h => hy (Subtype.ext h)) n,
    Iso.hom_inv_id, Category.comp_id]

/-- Restriction from a compact support to one of its points commutes
with the actual rational excision maps. -/
@[reassoc]
theorem rationalCompactSupportExcisionHomologyIso_toPoint
    (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (x : X) (hxK : x ∈ K) (n : ℕ) :
    (rationalCompactSupportExcisionHomologyIso X U K hK hU hKU n).hom ≫
        scalarLocalHomologyToPoint ℚ X K x hxK n =
      scalarLocalHomologyToPoint ℚ (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)
          (⟨x, hKU hxK⟩ : U) hxK n ≫
        (rationalLocalExcisionHomologyIso X U x (hKU hxK) hU n).hom := by
  rw [rationalCompactSupportExcisionHomologyIso_hom, rationalLocalExcisionHomologyIso_hom]
  unfold scalarLocalHomologyToPoint
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    RelativeScalarChains.Cycles.relativeScalarChainsMap_comp, RelativeScalarChains.Cycles.relativeScalarChainsMap_comp]
  simp only [Category.comp_id, Category.id_comp]

/-- The point restriction of the compact relative trace is the ordinary
point projection transported into the open neighborhood by local excision. -/
@[reassoc]
theorem compactRelativeTrace_toPoint (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (x : X) (hxK : x ∈ K) (n : ℕ) :
    compactRelativeTrace X U K hK hU hKU n ≫
        scalarLocalHomologyToPoint ℚ (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)
          (⟨x, hKU hxK⟩ : U) hxK n =
      HomologicalComplex.homologyMap
          (RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X ({x}ᶜ : Set X)) n ≫
        (rationalLocalExcisionHomologyIso X U x (hKU hxK) hU n).inv := by
  apply (cancel_mono (rationalLocalExcisionHomologyIso X U x (hKU hxK) hU n).hom).mp
  rw [Category.assoc,
    ← rationalCompactSupportExcisionHomologyIso_toPoint X U K hK hU hKU x hxK n,
    ← Category.assoc, compactRelativeTrace_excision,
    scalarLocalHomologyToPoint_projection, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- On an ordinary homology class, inclusion into locally finite chains
followed by the genuine finite compact restriction gives the same trace.
This uses the proved finite truncation identity, not a localization map
on locally finite homology. -/
theorem compactRelativeTrace_eq_locallyFiniteRestriction
    (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    compactRelativeTrace X U K hK hU hKU n =
      HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℚ X) n ≫
        LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ X K hK n ≫
          (rationalCompactSupportExcisionHomologyIso X U K hK hU hKU n).inv := by
  rw [← Category.assoc, LocallyFiniteScalarRestriction.Cycles.ordinaryToLocallyFinite_comp_scalarCompactHomologyRestriction]
  rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace
