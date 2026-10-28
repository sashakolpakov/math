import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Topology.Category.TopCat.EpiMono

/-! # Local Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles

noncomputable section

section

/-!
# Relative singular chains and local homology

These are genuine integral singular chains. For a subspace `A ⊆ X`, relative
chains are the cokernel of the singular chain map of the continuous inclusion.
In particular, local homology at `x` means `Hₙ(X, X \ {x}; ℤ)`.

The short exact sequence below supplies the chain-level starting point for the
long exact sequence of a pair. It does not assert excision, a local orientation
theorem, a fundamental class, or Poincaré duality.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

/-- The ordinary integral singular chain functor already constructed by mathlib. -/
abbrev integralSingularChainFunctor : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- Ordinary integral singular chains, with the alternating face differential. -/
abbrev integralSingularChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  integralSingularChainFunctor.obj X

/-- Inclusion of a subspace with its induced topology. -/
def subspaceInclusion (X : TopCat.{0}) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance subspaceInclusion_mono (X : TopCat.{0}) (A : Set X) :
    Mono (subspaceInclusion X A) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The actual chain map induced by the inclusion `A ⊆ X`. -/
abbrev subspaceChainInclusion (X : TopCat.{0}) (A : Set X) :
    integralSingularChains (TopCat.of A) ⟶ integralSingularChains X :=
  integralSingularChainFunctor.map (subspaceInclusion X A)

instance subspaceChainInclusion_mono (X : TopCat.{0}) (A : Set X) :
    Mono (subspaceChainInclusion X A) := by
  dsimp [subspaceChainInclusion]
  infer_instance

/-- Relative integral singular chains, the quotient of `Cₙ(X)` by `Cₙ(A)`. -/
abbrev relativeSingularChains (X : TopCat.{0}) (A : Set X) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (subspaceChainInclusion X A)

/-- Projection from absolute to relative singular chains. -/
abbrev relativeChainProjection (X : TopCat.{0}) (A : Set X) :
    integralSingularChains X ⟶ relativeSingularChains X A :=
  cokernel.π (subspaceChainInclusion X A)

@[reassoc (attr := simp)]
theorem subspaceChainInclusion_projection (X : TopCat.{0}) (A : Set X) :
    subspaceChainInclusion X A ≫ relativeChainProjection X A = 0 :=
  cokernel.condition _

/-- The genuine singular-chain short complex for a pair of spaces. -/
def relativeChainSequence (X : TopCat.{0}) (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (subspaceChainInclusion X A) (relativeChainProjection X A)
    (subspaceChainInclusion_projection X A)

/-- The chain sequence `0 → C(A) → C(X) → C(X,A) → 0` is short exact. -/
theorem relativeChainSequence_shortExact (X : TopCat.{0}) (A : Set X) :
    (relativeChainSequence X A).ShortExact := by
  change (ShortComplex.mk (subspaceChainInclusion X A)
    (cokernel.π (subspaceChainInclusion X A)) _).ShortExact
  exact { exact := ShortComplex.cokernelSequence_exact (subspaceChainInclusion X A) }

/-- The relative-chain sequence is also short exact in every individual degree. -/
theorem relativeChainSequence_degreewiseShortExact (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ((relativeChainSequence X A).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (relativeChainSequence_shortExact X A) n

/-- Integral relative singular homology. -/
abbrev relativeSingularHomology (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ModuleCat.{0} ℤ :=
  (relativeSingularChains X A).homology n

/-- Local integral singular homology at a point, with the punctured subspace. -/
abbrev localSingularHomology (X : TopCat.{0}) (x : X) (n : ℕ) : ModuleCat.{0} ℤ :=
  relativeSingularHomology X ({x}ᶜ : Set X) n

/-- A continuous map restricting to the indicated subspaces. -/
def subspaceMap {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun a ↦ ⟨f a, h a.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[reassoc]
theorem subspaceMap_inclusion {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    subspaceMap f h ≫ subspaceInclusion Y B = subspaceInclusion X A ≫ f := by
  rfl

/-- Functoriality of actual relative singular chains for a map of pairs. -/
def relativeSingularChainsMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    relativeSingularChains X A ⟶ relativeSingularChains Y B :=
  cokernel.map (subspaceChainInclusion X A) (subspaceChainInclusion Y B)
    (integralSingularChainFunctor.map (subspaceMap f h))
    (integralSingularChainFunctor.map f) (by
      rw [← Functor.map_comp, ← Functor.map_comp, subspaceMap_inclusion])

@[reassoc (attr := simp)]
theorem relativeChainProjection_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    relativeChainProjection X A ≫ relativeSingularChainsMap f h =
      integralSingularChainFunctor.map f ≫ relativeChainProjection Y B := by
  exact cokernel.π_desc _ _ _

/-- The induced homomorphism of integral relative singular homology groups. -/
abbrev relativeSingularHomologyMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ) :
    relativeSingularHomology X A n ⟶ relativeSingularHomology Y B n :=
  HomologicalComplex.homologyMap (relativeSingularChainsMap f h) n

/-- Homeomorphisms of pairs induce isomorphisms of the relative chain complexes. -/
def relativeSingularChainsIso {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ e x ∈ B) :
    relativeSingularChains X A ≅ relativeSingularChains Y B := by
  let f := (TopCat.isoOfHomeo e).hom
  have hm : Set.MapsTo f A B := fun x hx ↦ (h x).mp hx
  have hs : subspaceMap f hm = (TopCat.isoOfHomeo (e.subtype h)).hom := by
    ext a
    rfl
  letI : IsIso (subspaceMap f hm) := by
    rw [hs]
    infer_instance
  letI : IsIso (relativeSingularChainsMap f hm) := by
    dsimp [relativeSingularChainsMap]
    infer_instance
  exact asIso (relativeSingularChainsMap f hm)

/-- Homeomorphism invariance of integral relative singular homology. -/
def relativeSingularHomologyIso {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    relativeSingularHomology X A n ≅ relativeSingularHomology Y B n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (relativeSingularChainsIso e h)

/-- Local homology is transported by an actual homeomorphism. -/
def localSingularHomologyIso {X Y : TopCat.{0}} (e : X ≃ₜ Y) (x : X) (n : ℕ) :
    localSingularHomology X x n ≅ localSingularHomology Y (e x) n :=
  relativeSingularHomologyIso e (by
    intro y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, e.injective.eq_iff]) n

end

/-!
# Functoriality of the actual relative singular-chain quotient

The maps here are the existing cokernel maps induced by continuous maps of
pairs. Their identity and composition laws follow from the actual relative
chain projections, which are epimorphisms.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The identity map of a pair induces the identity on relative chains. -/
@[simp]
theorem relativeSingularChainsMap_id (X : TopCat.{0}) (A : Set X) :
    relativeSingularChainsMap (𝟙 X) (A := A) (B := A) (fun _ hx => hx) =
      𝟙 (relativeSingularChains X A) := by
  apply (cancel_epi (relativeChainProjection X A)).mp
  rw [relativeChainProjection_naturality, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]

/-- Composition of maps of pairs gives composition of the actual relative
singular-chain maps. -/
@[reassoc]
theorem relativeSingularChainsMap_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    relativeSingularChainsMap f hf ≫ relativeSingularChainsMap g hg =
      relativeSingularChainsMap (f ≫ g) (fun _ hx => hg (hf hx)) := by
  apply (cancel_epi (relativeChainProjection X A)).mp
  rw [← Category.assoc, relativeChainProjection_naturality, Category.assoc,
    relativeChainProjection_naturality, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    relativeChainProjection_naturality]

/-- The identity map of a pair acts identically on its actual relative homology. -/
@[simp]
theorem relativeSingularHomologyMap_id (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeSingularHomologyMap (𝟙 X) (A := A) (B := A) (fun _ hx => hx) n =
      𝟙 (relativeSingularHomology X A n) := by
  change HomologicalComplex.homologyMap _ n = _
  rw [relativeSingularChainsMap_id, HomologicalComplex.homologyMap_id]

/-- Relative homology maps compose as the underlying continuous maps of pairs. -/
@[reassoc]
theorem relativeSingularHomologyMap_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (n : ℕ) :
    relativeSingularHomologyMap f hf n ≫ relativeSingularHomologyMap g hg n =
      relativeSingularHomologyMap (f ≫ g) (fun _ hx => hg (hf hx)) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, relativeSingularChainsMap_comp]

/-- The existing homeomorphism comparison is induced by its forward map of pairs. -/
@[simp]
theorem relativeSingularChainsIso_hom {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ e x ∈ B) :
    (relativeSingularChainsIso e h).hom =
      relativeSingularChainsMap (TopCat.isoOfHomeo e).hom (fun x hx => (h x).mp hx) := rfl

/-- The homeomorphism comparison on relative homology is the usual induced map. -/
@[simp]
theorem relativeSingularHomologyIso_hom {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    (relativeSingularHomologyIso e h n).hom =
      relativeSingularHomologyMap (TopCat.isoOfHomeo e).hom (fun x hx => (h x).mp hx) n := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles
