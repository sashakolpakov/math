import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex

/-! # Locally Finite Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles

noncomputable section

/-!
# Comparing ordinary and spatially locally finite singular chain complexes

The inclusion preserves actual simplex coefficients. Its compatibility with
the differential is proved from finite-fiber pushforward on individual
simplex generators. On compact spaces it is an isomorphism of chain complexes,
and hence induces the corresponding isomorphism on homology.
-/

open Set Function _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial BigOperators

namespace SpatialSupport

variable {X ι κ : Type*} [TopologicalSpace X]
variable {R : Type*} [Semiring R]

/-- Finite-fiber coefficient pushforward sends a single simplex coefficient
to the single coefficient at its image. -/
theorem pushforward_ofFinsupp_single {imageA : ι → Set X} {imageB : κ → Set X}
    (f : ι → κ) (himage : ∀ i, imageB (f i) ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (i : ι) (r : R) :
    LocallyFiniteChains.Cycles.SpatialSupport.pushforward f himage hne (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA (Finsupp.single i r)) =
      LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageB (Finsupp.single (f i) r) := by
  classical
  apply Subtype.ext
  funext j
  change (∑ᶠ k ∈ {k | f k = j}, (Finsupp.single i r : ι →₀ R) k) =
    (Finsupp.single (f i) r : κ →₀ R) j
  rw [finsum_mem_def, finsum_eq_single _ i]
  · simp [Set.indicator_apply, Finsupp.single_apply, eq_comm]
  · intro k hk
    simp [Set.indicator_apply, hk]

/-- On finitely supported coefficients, the spatial pushforward agrees with
the standard finite sum over the index-map fibers. -/
theorem pushforward_ofFinsupp {imageA : ι → Set X} {imageB : κ → Set X}
    (f : ι → κ) (himage : ∀ i, imageB (f i) ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) :
    (LocallyFiniteChains.Cycles.SpatialSupport.pushforward f himage hne).comp (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA) =
      (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageB).comp (Finsupp.lmapDomain R R f) := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext
  intro r
  simpa only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using
      pushforward_ofFinsupp_single f himage hne i r

end SpatialSupport

variable (R : Type) [CommRing R] (X : TopCat.{0})

/-- A simplex generator viewed in the locally finite coefficient module. -/
def locallyFiniteGenerator (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    ModuleCat.of R R ⟶ ModuleCat.of R (LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n) :=
  ModuleCat.ofHom ((LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp (LocallyFiniteChains.Cycles.singularSimplexImage X n)).comp
    (Finsupp.lsingle σ (R := R)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical coproduct coordinates preserve each actual simplex generator. -/
@[reassoc]
theorem ordinarySingularChainCoefficients_simplex (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ ≫
      ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n).toLinearMap =
        ModuleCat.ofHom (Finsupp.lsingle σ (R := R) (M := ModuleCat.of R R)) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of R R) n).comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit R R ((TopCat.toSSet.obj X).obj (.op ⦋n⦌)))
      (Discrete.mk σ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The existing ordinary-to-locally-finite degree map sends each generator
to its literal singleton coefficient function. -/
@[reassoc]
theorem ordinaryToLocallyFinite_simplex (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ ≫
      ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n) =
        locallyFiniteGenerator R X n σ := by
  unfold LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite locallyFiniteGenerator
  rw [ModuleCat.ofHom_comp, ← Category.assoc,
    ordinarySingularChainCoefficients_simplex, ModuleCat.ofHom_comp]

/-- The face map on locally finite coefficients has the usual action on an
individual simplex generator. -/
@[reassoc]
theorem locallyFiniteGenerator_face (n : ℕ) (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n + 1⦌)) :
    locallyFiniteGenerator R X (n + 1) σ ≫
      ModuleCat.ofHom (LocallyFiniteChains.Cycles.locallyFiniteFace R X n i) =
        locallyFiniteGenerator R X n ((TopCat.toSSet.obj X).δ i σ) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact SpatialSupport.pushforward_ofFinsupp_single ((TopCat.toSSet.obj X).δ i)
    (LocallyFiniteChains.Cycles.singularSimplexImage_face_subset X n i) (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty X n) σ r

set_option backward.isDefEq.respectTransparency false in
/-- The categorical differential is the alternating sum of the actual face maps. -/
theorem locallyFiniteSingularComplex_d_hom (n : ℕ) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ModuleCat.ofHom (LocallyFiniteChains.Cycles.locallyFiniteFace R X n i) := by
  apply ModuleCat.hom_ext
  simpa only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom] using
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d_int R X n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The locally finite differential has the ordinary simplex boundary on generators. -/
@[reassoc]
theorem locallyFiniteGenerator_d (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n + 1⦌)) :
    locallyFiniteGenerator R X (n + 1) σ ≫
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          locallyFiniteGenerator R X n ((TopCat.toSSet.obj X).δ i σ) := by
  rw [locallyFiniteSingularComplex_d_hom]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, locallyFiniteGenerator_face]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The coefficient inclusion commutes with the actual singular differentials. -/
theorem ordinaryToLocallyFinite_comm (n : ℕ) :
    ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (n + 1)) ≫
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (n + 1) n =
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d (n + 1) n ≫
          ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n) := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ordinaryToLocallyFinite_simplex,
    locallyFiniteGenerator_d, ← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ordinaryToLocallyFinite_simplex]

/-- No ordinary chain coefficients are lost by the canonical inclusion. -/
theorem ordinaryToLocallyFinite_injective (n : ℕ) :
    Function.Injective (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n) :=
  (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp_injective (LocallyFiniteChains.Cycles.singularSimplexImage X n)).comp
    (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n).injective

/-- The canonical inclusion of ordinary singular chains into spatially locally finite
singular chains, with its proved boundary compatibility. -/
def ordinaryToLocallyFiniteChainMap :
    (TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R) ⟶
      LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X where
  f n := ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    exact ordinaryToLocallyFinite_comm R X j

@[simp]
theorem ordinaryToLocallyFiniteChainMap_f (n : ℕ) :
    (ordinaryToLocallyFiniteChainMap R X).f n =
      ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On a compact space every spatially locally finite chain has finite support.
The canonical inclusion is consequently an isomorphism of the actual chain complexes. -/
def ordinaryLocallyFiniteChainIso [CompactSpace X] :
    (TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R) ≅
      LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (LocallyFiniteCompact.Cycles.locallyFiniteOrdinaryEquiv R X n).symm.toModuleIso)
    (by
      intro i j hij
      change ModuleCat.ofHom (LocallyFiniteCompact.Cycles.locallyFiniteOrdinaryEquiv R X i).symm.toLinearMap ≫
          (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d i j =
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d i j ≫
          ModuleCat.ofHom (LocallyFiniteCompact.Cycles.locallyFiniteOrdinaryEquiv R X j).symm.toLinearMap
      rw [LocallyFiniteCompact.Cycles.locallyFiniteOrdinaryEquiv_symm, LocallyFiniteCompact.Cycles.locallyFiniteOrdinaryEquiv_symm]
      exact (ordinaryToLocallyFiniteChainMap R X).comm' i j hij)

set_option backward.isDefEq.respectTransparency false in
/-- The compact-space isomorphism uses the same canonical chain inclusion. -/
@[simp]
theorem ordinaryLocallyFiniteChainIso_hom [CompactSpace X] :
    (ordinaryLocallyFiniteChainIso R X).hom = ordinaryToLocallyFiniteChainMap R X := by
  apply HomologicalComplex.hom_ext
  intro n
  change ModuleCat.ofHom (LocallyFiniteCompact.Cycles.locallyFiniteOrdinaryEquiv R X n).symm.toLinearMap =
    ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n)
  rw [LocallyFiniteCompact.Cycles.locallyFiniteOrdinaryEquiv_symm]

/-- The inverse compact comparison, from locally finite chains to ordinary chains. -/
def locallyFiniteOrdinaryChainIso [CompactSpace X] :
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X ≅
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R) :=
  (ordinaryLocallyFiniteChainIso R X).symm

/-- Compact-space comparison on the homology of the two actual singular chain complexes. -/
def ordinaryLocallyFiniteHomologyIso [CompactSpace X] (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).homology n ≅
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (ordinaryLocallyFiniteChainIso R X)

/-- The inverse compact comparison on locally finite singular homology. -/
def locallyFiniteOrdinaryHomologyIso [CompactSpace X] (n : ℕ) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).homology n :=
  (ordinaryLocallyFiniteHomologyIso R X n).symm

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles
