import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import OAI.AlgebraicTopology.Cohomology.Singular.Evaluation

/-! # Relative Scalar Chains -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles

/-!
# Relative singular chains with scalar coefficients

These are the actual scalar singular chains of a pair, defined by the cokernel
of the map from the subspace. Their degreewise quotient description follows
from the genuine short exact sequence. At integral coefficients the objects
are definitionally the relative chain models used in the local homology
calculation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

variable (R : Type) [CommRing R]

/-- The existing scalar singular-chain functor. -/
abbrev scalarSingularChainFunctor : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} R) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)

/-- The actual singular chain map of the subspace inclusion. -/
abbrev scalarSubspaceChainInclusion (X : TopCat.{0}) (A : Set X) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of A) ⟶
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X :=
  (scalarSingularChainFunctor R).map (LocalHomology.Cycles.subspaceInclusion X A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance scalarSubspaceChainInclusion_mono (X : TopCat.{0}) (A : Set X) :
    Mono (scalarSubspaceChainInclusion R X A) := by
  exact Functor.map_mono
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R))
    (LocalHomology.Cycles.subspaceInclusion X A)

/-- Relative scalar chains are the actual cokernel of the subspace-chain map. -/
abbrev relativeScalarChains (X : TopCat.{0}) (A : Set X) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  cokernel (scalarSubspaceChainInclusion R X A)

/-- The actual quotient map to relative scalar chains. -/
abbrev relativeScalarChainProjection (X : TopCat.{0}) (A : Set X) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X ⟶ relativeScalarChains R X A :=
  cokernel.π (scalarSubspaceChainInclusion R X A)

@[reassoc (attr := simp)]
theorem scalarSubspaceChainInclusion_projection (X : TopCat.{0}) (A : Set X) :
    scalarSubspaceChainInclusion R X A ≫ relativeScalarChainProjection R X A = 0 :=
  cokernel.condition _

/-- The short complex underlying the scalar singular-chain sequence of a pair. -/
def relativeScalarChainSequence (X : TopCat.{0}) (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk (scalarSubspaceChainInclusion R X A) (relativeScalarChainProjection R X A)
    (scalarSubspaceChainInclusion_projection R X A)

/-- The scalar pair sequence is short exact. -/
theorem relativeScalarChainSequence_shortExact (X : TopCat.{0}) (A : Set X) :
    (relativeScalarChainSequence R X A).ShortExact := by
  change (ShortComplex.mk (scalarSubspaceChainInclusion R X A)
    (cokernel.π (scalarSubspaceChainInclusion R X A)) _).ShortExact
  exact { exact := ShortComplex.cokernelSequence_exact (scalarSubspaceChainInclusion R X A) }

/-- The actual pair sequence is short exact in each chain degree. -/
theorem relativeScalarChainSequence_degreewiseShortExact
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ((relativeScalarChainSequence R X A).map
      (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.down ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (relativeScalarChainSequence_shortExact R X A) n

instance relativeScalarChainProjection_f_epi (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Epi ((relativeScalarChainProjection R X A).f n) :=
  (relativeScalarChainSequence_degreewiseShortExact R X A n).epi_g

/-- Every relative chain is the projection of an actual absolute chain. -/
theorem relativeScalarChainProjection_surjective (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Function.Surjective ((relativeScalarChainProjection R X A).f n) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- A chain maps to zero in the relative quotient exactly when it comes from
the actual subspace chain complex. -/
theorem relativeScalarChainProjection_ker (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.ker ((relativeScalarChainProjection R X A).f n).hom =
      LinearMap.range ((scalarSubspaceChainInclusion R X A).f n).hom :=
  (relativeScalarChainSequence_degreewiseShortExact R X A n).exact.moduleCat_range_eq_ker.symm

/-- Genuine relative singular homology over the scalar coefficient ring. -/
abbrev relativeScalarHomology (X : TopCat.{0}) (A : Set X) (n : ℕ) : ModuleCat.{0} R :=
  (relativeScalarChains R X A).homology n

/-- Genuine local scalar homology is the homology relative to the punctured space. -/
abbrev localScalarHomology (X : TopCat.{0}) (x : X) (n : ℕ) : ModuleCat.{0} R :=
  relativeScalarHomology R X ({x}ᶜ : Set X) n

/-- A continuous map of pairs gives the actual map of scalar relative chains. -/
def relativeScalarChainsMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    relativeScalarChains R X A ⟶ relativeScalarChains R Y B :=
  cokernel.map (scalarSubspaceChainInclusion R X A) (scalarSubspaceChainInclusion R Y B)
    ((scalarSingularChainFunctor R).map (LocalHomology.Cycles.subspaceMap f h))
    ((scalarSingularChainFunctor R).map f) (by
      change (scalarSingularChainFunctor R).map (LocalHomology.Cycles.subspaceInclusion X A) ≫
          (scalarSingularChainFunctor R).map f =
        (scalarSingularChainFunctor R).map (LocalHomology.Cycles.subspaceMap f h) ≫
          (scalarSingularChainFunctor R).map (LocalHomology.Cycles.subspaceInclusion Y B)
      rw [← Functor.map_comp, ← Functor.map_comp, LocalHomology.Cycles.subspaceMap_inclusion])

@[reassoc (attr := simp)]
theorem relativeScalarChainProjection_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    relativeScalarChainProjection R X A ≫ relativeScalarChainsMap R f h =
      (scalarSingularChainFunctor R).map f ≫ relativeScalarChainProjection R Y B :=
  cokernel.π_desc _ _ _

/-- Integral specialization is exactly the established relative singular complex. -/
theorem relativeScalarChains_int (X : TopCat.{0}) (A : Set X) :
    relativeScalarChains ℤ X A = LocalHomology.Cycles.relativeSingularChains X A := rfl

/-- Integral specialization gives exactly the established quotient map. -/
theorem relativeScalarChainProjection_int (X : TopCat.{0}) (A : Set X) :
    relativeScalarChainProjection ℤ X A = LocalHomology.Cycles.relativeChainProjection X A := rfl

end AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles

namespace AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-!
# Functoriality of actual scalar relative singular chains

Identity and composition follow from the actual cokernel projections.
The homology composition law therefore concerns the same scalar maps used
in the two-support cap product.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable (R : Type) [CommRing R]

@[simp]
theorem relativeScalarChainsMap_id (X : TopCat.{0}) (A : Set X) :
    relativeScalarChainsMap R (𝟙 X) (A := A) (B := A) (fun _ hx => hx) =
      𝟙 (relativeScalarChains R X A) := by
  apply (cancel_epi (relativeScalarChainProjection R X A)).mp
  rw [relativeScalarChainProjection_naturality, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

@[reassoc]
theorem relativeScalarChainsMap_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    relativeScalarChainsMap R f hf ≫ relativeScalarChainsMap R g hg =
      relativeScalarChainsMap R (f ≫ g) (fun _ hx => hg (hf hx)) := by
  apply (cancel_epi (relativeScalarChainProjection R X A)).mp
  rw [← Category.assoc, relativeScalarChainProjection_naturality, Category.assoc,
    relativeScalarChainProjection_naturality, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, relativeScalarChainProjection_naturality]

@[reassoc]
theorem relativeScalarHomologyMap_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeScalarChainsMap R f hf) n ≫
        HomologicalComplex.homologyMap (relativeScalarChainsMap R g hg) n =
      HomologicalComplex.homologyMap
        (relativeScalarChainsMap R (f ≫ g) (fun _ hx => hg (hf hx))) n := by
  rw [← HomologicalComplex.homologyMap_comp, relativeScalarChainsMap_comp]

end Cycles

end AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

end

end OAI
