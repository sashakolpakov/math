import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap

/-! # Locally Finite Comparison Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparisonNaturality.Cycles

noncomputable section

/-!
# Naturality of the ordinary / locally finite singular-chain comparison

Proper pushforward agrees with ordinary singular-chain pushforward on finitely
supported chains. The actual comparison chain map and the compact comparison
isomorphisms therefore commute with proper pushforward, as do their induced
maps on homology.
-/

open Set Function _root_.CategoryTheory
open scoped Simplicial

namespace SpatialSupport

variable {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {R : Type*} [Semiring R]

/-- Transporting a finite chain's spatial support leaves its literal
coefficient function unchanged. -/
theorem properImageCoefficients_ofFinsupp (f : X → Y) (hf : IsProperMap f)
    (imageA : ι → Set X) :
    (LocallyFiniteProperMap.Cycles.SpatialSupport.properImageCoefficients (R := R) f hf imageA).comp (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA) =
      LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp (fun i => f '' imageA i) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  rfl

/-- Proper pushforward sends a singleton coefficient to the singleton
coefficient at its actual image. -/
theorem properPushforward_ofFinsupp_single (f : X → Y) (hf : IsProperMap f)
    {imageA : ι → Set X} {imageB : κ → Set Y} (g : ι → κ)
    (himage : ∀ i, imageB (g i) ⊆ f '' imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (i : ι) (r : R) :
    LocallyFiniteProperMap.Cycles.SpatialSupport.properPushforward f hf g himage hne (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA (Finsupp.single i r)) =
      LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageB (Finsupp.single (g i) r) :=
  LocallyFiniteComparison.Cycles.SpatialSupport.pushforward_ofFinsupp_single g himage hne i r

/-- On finite chains proper coefficient pushforward is the usual finite
sum over the fibers of the index map. -/
theorem properPushforward_ofFinsupp (f : X → Y) (hf : IsProperMap f)
    {imageA : ι → Set X} {imageB : κ → Set Y} (g : ι → κ)
    (himage : ∀ i, imageB (g i) ⊆ f '' imageA i)
    (hne : ∀ j, (imageB j).Nonempty) :
    (LocallyFiniteProperMap.Cycles.SpatialSupport.properPushforward f hf g himage hne).comp (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA) =
      (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageB).comp (Finsupp.lmapDomain R R g) := by
  unfold LocallyFiniteProperMap.Cycles.SpatialSupport.properPushforward
  rw [LinearMap.comp_assoc, properImageCoefficients_ofFinsupp,
    LocallyFiniteComparison.Cycles.SpatialSupport.pushforward_ofFinsupp]

end SpatialSupport

variable (R : Type) [CommRing R] {X Y : TopCat.{0}}

/-- Proper singular pushforward acts on a simplex generator by actual
postcomposition of that simplex. -/
@[reassoc]
theorem locallyFiniteGenerator_proper (f : X ⟶ Y) (hf : IsProperMap f)
    (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    LocallyFiniteComparison.Cycles.locallyFiniteGenerator R X n σ ≫ ModuleCat.ofHom (LocallyFiniteProperMap.Cycles.locallyFiniteProperMap R f hf n) =
      LocallyFiniteComparison.Cycles.locallyFiniteGenerator R Y n ((TopCat.toSSet.map f).app (.op ⦋n⦌) σ) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact SpatialSupport.properPushforward_ofFinsupp_single f hf
    ((TopCat.toSSet.map f).app (.op ⦋n⦌))
    (fun τ => (LocallyFiniteProperMap.Cycles.singularSimplexImage_postcompose f n τ).le)
    (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty Y n) σ r

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The ordinary-to-locally-finite comparison commutes with every genuine
proper continuous map, without compactness assumptions on either space. -/
@[reassoc]
theorem ordinaryToLocallyFiniteChainMap_naturality (f : X ⟶ Y)
    (hf : IsProperMap f) :
    SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R) ≫
        LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R Y =
      LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X ≫ LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap R f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  change (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f n ≫
      ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R Y n) =
    ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n) ≫
      ModuleCat.ofHom (LocallyFiniteProperMap.Cycles.locallyFiniteProperMap R f hf n)
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro σ
  simp only [← Category.assoc, SSet.ι_chainComplexMap_f,
    LocallyFiniteComparison.Cycles.ordinaryToLocallyFinite_simplex, locallyFiniteGenerator_proper]

/-- The actual homology map induced by the ordinary-to-locally-finite inclusion. -/
abbrev ordinaryToLocallyFiniteHomologyMap (X : TopCat.{0}) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).homology n ⟶
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n :=
  HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X) n

/-- Proper naturality also holds on the homology of the actual chain complexes. -/
@[reassoc]
theorem ordinaryToLocallyFiniteHomologyMap_naturality (f : X ⟶ Y)
    (hf : IsProperMap f) (n : ℕ) :
    HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)) n ≫
        ordinaryToLocallyFiniteHomologyMap R Y n =
      ordinaryToLocallyFiniteHomologyMap R X n ≫
        LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f hf n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (ordinaryToLocallyFiniteChainMap_naturality R f hf)

/-- On compact spaces the forward comparison isomorphism is natural for proper maps. -/
@[reassoc]
theorem ordinaryLocallyFiniteChainIso_naturality [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (hf : IsProperMap f) :
    SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R) ≫
        (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R Y).hom =
      (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R X).hom ≫ LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap R f hf := by
  simpa only [LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso_hom] using
    ordinaryToLocallyFiniteChainMap_naturality R f hf

/-- The inverse compact comparison also commutes with proper pushforward. -/
@[reassoc]
theorem locallyFiniteOrdinaryChainIso_naturality [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (hf : IsProperMap f) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap R f hf ≫ (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso R Y).hom =
      (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso R X).hom ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R) := by
  change LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap R f hf ≫ (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R Y).inv =
    (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R X).inv ≫
      SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)
  calc
    _ = (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R X).inv ≫
        ((LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R X).hom ≫ LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap R f hf) ≫
          (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R Y).inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R X).inv ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R) ≫
          (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R Y).hom) ≫
          (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R Y).inv := by
      rw [ordinaryLocallyFiniteChainIso_naturality]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Forward compact comparison on homology commutes with proper pushforward. -/
@[reassoc]
theorem ordinaryLocallyFiniteHomologyIso_naturality [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)) n ≫
        (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteHomologyIso R Y n).hom =
      (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteHomologyIso R X n).hom ≫
        LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f hf n := by
  change HomologicalComplex.homologyMap
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)) n ≫
      HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R Y).hom n =
    HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso R X).hom n ≫
      HomologicalComplex.homologyMap (LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap R f hf) n
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (ordinaryLocallyFiniteChainIso_naturality R f hf)

/-- A locally finite homology class pushed forward and then converted to
ordinary homology is the ordinary pushforward of its converted class. -/
@[reassoc]
theorem locallyFiniteOrdinaryHomologyIso_naturality [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f hf n ≫
        (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso R Y n).hom =
      (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso R X n).hom ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)) n := by
  change HomologicalComplex.homologyMap (LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap R f hf) n ≫
      HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso R Y).hom n =
    HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso R X).hom n ≫
      HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)) n
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (locallyFiniteOrdinaryChainIso_naturality R f hf)

/-- Elementwise proper naturality of the compact homology comparison. -/
theorem locallyFiniteOrdinaryHomologyIso_naturality_apply
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ)
    (c : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n) :
    (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso R Y n).hom
        (LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f hf n c) =
      HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)) n
        ((LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso R X n).hom c) :=
  ConcreteCategory.congr_hom (locallyFiniteOrdinaryHomologyIso_naturality R f hf n) c

/-- For a continuous map from a compact source into a compact Hausdorff
ambient space, properness is automatic. The converted pushforward of every
locally finite class equals its actual ordinary singular-homology pushforward. -/
theorem compactLocallyFiniteOrdinaryHomology_naturality
    [CompactSpace X] [CompactSpace Y] [T2Space Y] (f : X ⟶ Y) (n : ℕ)
    (c : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n) :
    (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso R Y n).hom
        (LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f f.hom.continuous.isProperMap n c) =
      HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)) n
        ((LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso R X n).hom c) :=
  locallyFiniteOrdinaryHomologyIso_naturality_apply R f f.hom.continuous.isProperMap n c

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparisonNaturality.Cycles
