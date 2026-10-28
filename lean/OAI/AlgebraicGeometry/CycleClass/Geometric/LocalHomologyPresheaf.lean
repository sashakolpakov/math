import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import Mathlib.Topology.Sheaves.Stalks

/-! # Local Homology Presheaf -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles

noncomputable section

/-!
# The presheaf of local relative singular homology

The value on an open set `U` is the genuine relative group `H_n(X, X ∖ U; ℤ)`.
Inclusions `U ⊆ V` give restriction maps by the actual identity map of pairs
`(X, X ∖ V) → (X, X ∖ U)`. For every point, these maps define a canonical
comparison from the actual presheaf stalk to the local relative homology group.

No sheaf property or orientation assertion is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0})

/-- Restriction in a support set is the identity map of the complementary pairs. -/
def relativeComplementChainRestriction {U V : Set X} (hUV : U ⊆ V) :
    LocalHomology.Cycles.relativeSingularChains X Vᶜ ⟶ LocalHomology.Cycles.relativeSingularChains X Uᶜ :=
  LocalHomology.Cycles.relativeSingularChainsMap (𝟙 X) (fun _ hy hU => hy (hUV hU))

@[simp]
theorem relativeComplementChainRestriction_refl (U : Set X) :
    relativeComplementChainRestriction X (Set.Subset.refl U) =
      𝟙 (LocalHomology.Cycles.relativeSingularChains X Uᶜ) :=
  LocalHomology.Cycles.relativeSingularChainsMap_id X Uᶜ

/-- Restrictions compose with their actual identity maps of pairs. -/
theorem relativeComplementChainRestriction_trans {U V W : Set X}
    (hUV : U ⊆ V) (hVW : V ⊆ W) :
    relativeComplementChainRestriction X hVW ≫ relativeComplementChainRestriction X hUV =
      relativeComplementChainRestriction X (hUV.trans hVW) := by
  unfold relativeComplementChainRestriction
  rw [LocalHomology.Cycles.relativeSingularChainsMap_comp]
  simp only [Category.id_comp]

/-- Restriction commutes with projection of the same ordinary singular chain. -/
@[reassoc]
theorem relativeComplementChainRestriction_projection {U V : Set X} (hUV : U ⊆ V) :
    LocalHomology.Cycles.relativeChainProjection X Vᶜ ≫ relativeComplementChainRestriction X hUV =
      LocalHomology.Cycles.relativeChainProjection X Uᶜ := by
  unfold relativeComplementChainRestriction
  rw [LocalHomology.Cycles.relativeChainProjection_naturality, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The genuine presheaf of relative singular-chain complexes. -/
def localHomologyChainPresheaf :
    X.Presheaf (ChainComplex (ModuleCat.{0} ℤ) ℕ) where
  obj U := LocalHomology.Cycles.relativeSingularChains X (U.unop : Set X)ᶜ
  map f := relativeComplementChainRestriction X f.unop.le
  map_id U := relativeComplementChainRestriction_refl X (U.unop : Set X)
  map_comp f g := (relativeComplementChainRestriction_trans X g.unop.le f.unop.le).symm

/-- The actual local-homology presheaf, before any sheafification. -/
def localHomologyPresheaf (n : ℕ) : X.Presheaf (ModuleCat.{0} ℤ) :=
  localHomologyChainPresheaf X ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n

@[simp]
theorem localHomologyPresheaf_obj (n : ℕ) (U : Opens X) :
    (localHomologyPresheaf X n).obj (op U) =
      LocalHomology.Cycles.relativeSingularHomology X (U : Set X)ᶜ n := rfl

/-- The map to local chains at a point, induced by the identity of `X`. -/
def relativeComplementChainToPoint (U : Set X) (x : X) (hx : x ∈ U) :
    LocalHomology.Cycles.relativeSingularChains X Uᶜ ⟶ LocalHomology.Cycles.relativeSingularChains X ({x}ᶜ : Set X) :=
  LocalHomology.Cycles.relativeSingularChainsMap (𝟙 X) (by
    intro y hy
    change y ≠ x
    intro hyx
    exact hy (hyx.symm ▸ hx))

/-- Ordinary projection followed by restriction to a point is the ordinary
projection to the actual local relative-chain complex. -/
@[reassoc]
theorem relativeComplementChainToPoint_projection (U : Set X) (x : X) (hx : x ∈ U) :
    LocalHomology.Cycles.relativeChainProjection X Uᶜ ≫ relativeComplementChainToPoint X U x hx =
      LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X) := by
  unfold relativeComplementChainToPoint
  rw [LocalHomology.Cycles.relativeChainProjection_naturality, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The maps to local chains are compatible with every restriction. -/
theorem relativeComplementChainRestriction_toPoint {U V : Set X} (hUV : U ⊆ V)
    (x : X) (hx : x ∈ U) :
    relativeComplementChainRestriction X hUV ≫ relativeComplementChainToPoint X U x hx =
      relativeComplementChainToPoint X V x (hUV hx) := by
  unfold relativeComplementChainRestriction relativeComplementChainToPoint
  rw [LocalHomology.Cycles.relativeSingularChainsMap_comp]
  simp only [Category.id_comp]

/-- The induced map from relative homology over a support set to local homology. -/
def localHomologyToPoint (U : Set X) (x : X) (hx : x ∈ U) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X Uᶜ n ⟶ LocalHomology.Cycles.localSingularHomology X x n :=
  HomologicalComplex.homologyMap (relativeComplementChainToPoint X U x hx) n

/-- The compatible neighborhood maps form a cocone with actual local homology as vertex. -/
def localHomologyStalkCocone (x : X) (n : ℕ) :
    Cocone ((OpenNhds.inclusion x).op ⋙ localHomologyPresheaf X n) where
  pt := LocalHomology.Cycles.localSingularHomology X x n
  ι.app U := localHomologyToPoint X (U.unop.val : Set X) x U.unop.property n
  ι.naturality U V f := by
    change HomologicalComplex.homologyMap (relativeComplementChainRestriction X f.unop.le) n ≫
        HomologicalComplex.homologyMap
          (relativeComplementChainToPoint X (V.unop.val : Set X) x V.unop.property) n =
      HomologicalComplex.homologyMap
          (relativeComplementChainToPoint X (U.unop.val : Set X) x U.unop.property) n ≫ 𝟙 _
    rw [Category.comp_id, ← HomologicalComplex.homologyMap_comp,
      relativeComplementChainRestriction_toPoint]

/-- The canonical map from the genuine presheaf stalk to local relative homology. -/
def localHomologyStalkToPoint (x : X) (n : ℕ) :
    (localHomologyPresheaf X n).stalk x ⟶ LocalHomology.Cycles.localSingularHomology X x n :=
  colimit.desc _ (localHomologyStalkCocone X x n)

/-- The stalk comparison has precisely the expected values on actual germs. -/
@[reassoc]
theorem localHomologyStalkToPoint_germ (x : X) (n : ℕ) (U : Opens X) (hx : x ∈ U) :
    (localHomologyPresheaf X n).germ U x hx ≫ localHomologyStalkToPoint X x n =
      localHomologyToPoint X (U : Set X) x hx n :=
  colimit.ι_desc (localHomologyStalkCocone X x n) (op (⟨U, hx⟩ : OpenNhds x))

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles
