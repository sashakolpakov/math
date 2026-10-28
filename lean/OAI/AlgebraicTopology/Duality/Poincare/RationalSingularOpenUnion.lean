import OAI.AlgebraicTopology.Duality.Poincare.SingularOpenUnion
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Rational Singular Open Union -/

namespace OAI.AlgebraicTopology.Duality.Poincare.RationalSingularOpenUnion

noncomputable section

/-!
# Rational singular chains and homology on increasing open unions

The integral increasing-open-union theorem is transported through the actual
rational extension-of-scalars functor. Its checked natural comparison with
rational singular chains identifies every leg with the original inclusion.
Exactness of filtered module colimits then gives the same result on ordinary
rational singular homology.

Both the arbitrary open union and a cover of the whole ambient space are
handled, with explicit native chain and homology cocones.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine rational singular chain functor on open subspaces. -/
def rationalOpenChainFunctor (X : TopCat.{0}) :
    Opens X ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  Opens.toTopCat X ⋙ AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ

/-- Ordinary rational singular homology of actual open subspaces. -/
def rationalOpenHomologyFunctor (X : TopCat.{0}) (n : ℕ) :
    Opens X ⥤ ModuleCat.{0} ℚ :=
  rationalOpenChainFunctor X ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n

@[simp]
theorem rationalOpenHomologyFunctor_obj (X : TopCat.{0}) (n : ℕ) (U : Opens X) :
    (rationalOpenHomologyFunctor X n).obj U =
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).homology n := rfl

/-- The open-subspace homology functor uses the actual continuous inclusion. -/
@[simp]
theorem rationalOpenHomologyFunctor_map (X : TopCat.{0}) (n : ℕ)
    {U V : Opens X} (h : U ≤ V) :
    (rationalOpenHomologyFunctor X n).map (homOfLE h) =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (TopCat.ofHom (ContinuousMap.inclusion h)) n := rfl

variable {X : TopCat.{0}} (U : ℕ → Opens X) (hU : Monotone U)

/-- The increasing diagram uses the same indexing functor as compact support. -/
def rationalIncreasingOpenChainDiagram : ℕ ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  hU.functor ⋙ rationalOpenChainFunctor X

/-- The increasing ordinary homology diagram, with native inclusion maps. -/
def rationalIncreasingOpenHomologyDiagram (n : ℕ) : ℕ ⥤ ModuleCat.{0} ℚ :=
  hU.functor ⋙ rationalOpenHomologyFunctor X n

@[simp]
theorem rationalIncreasingOpenChainDiagram_obj (i : ℕ) :
    (rationalIncreasingOpenChainDiagram U hU).obj i =
      Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U i)) := rfl

@[simp]
theorem rationalIncreasingOpenChainDiagram_map {i j : ℕ} (hij : i ≤ j) :
    (rationalIncreasingOpenChainDiagram U hU).map (homOfLE hij) =
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (Cohomology.Singular.IncreasingCochains.increasingOpenInclusion U hU hij) := rfl

@[simp]
theorem rationalIncreasingOpenHomologyDiagram_obj (n i : ℕ) :
    (rationalIncreasingOpenHomologyDiagram U hU n).obj i =
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U i))).homology n := rfl

@[simp]
theorem rationalIncreasingOpenHomologyDiagram_map (n : ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    (rationalIncreasingOpenHomologyDiagram U hU n).map (homOfLE hij) =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (Cohomology.Singular.IncreasingCochains.increasingOpenInclusion U hU hij) n := rfl

/-- The checked coefficient comparison identifies the whole rationalized
integral diagram with the genuine rational singular chain diagram. -/
def rationalIncreasingOpenChainDiagramIso :
    SingularOpenUnion.increasingOpenChainDiagram U hU ⋙
        AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      rationalIncreasingOpenChainDiagram U hU :=
  NatIso.ofComponents (fun i => AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso (TopCat.of (U i)))
    (fun {_i _j} f => AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality
      ((Opens.toTopCat X).map (hU.functor.map f)))

/-- The chain cocone into the ambient space consists of the original
rational singular chain maps of the open inclusions. -/
def rationalIncreasingOpenChainCocone : Cocone (rationalIncreasingOpenChainDiagram U hU) where
  pt := Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X
  ι := {
    app i := Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (U i).inclusion'
    naturality _i _j f := by
      change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
          ((Opens.toTopCat X).map (hU.functor.map f)) ≫
          (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (U _j).inclusion' =
        (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (U _i).inclusion' ≫ 𝟙 _
      rw [Category.comp_id, ← CategoryTheory.Functor.map_comp]
      congr 1 }

/-- The actual chain cocone into the increasing union. -/
def rationalOpenUnionChainCocone : Cocone (rationalIncreasingOpenChainDiagram U hU) where
  pt := Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (⨆ i, U i : Opens X))
  ι := {
    app i := Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (SingularOpenUnion.openUnionStageInclusion U i)
    naturality _i _j f := by
      change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
          ((Opens.toTopCat X).map (hU.functor.map f)) ≫
          (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (SingularOpenUnion.openUnionStageInclusion U _j) =
        (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (SingularOpenUnion.openUnionStageInclusion U _i) ≫ 𝟙 _
      rw [Category.comp_id, ← CategoryTheory.Functor.map_comp]
      congr 1 }

/-- Actual rational singular chains form the colimit over an increasing
open cover, by colimit-preserving scalar extension of the integral result. -/
def rationalIncreasingOpenChainIsColimit (hcover : (⨆ i, U i) = ⊤) :
    IsColimit (rationalIncreasingOpenChainCocone U hU) := by
  apply (IsColimit.precomposeHomEquiv (rationalIncreasingOpenChainDiagramIso U hU)
    (rationalIncreasingOpenChainCocone U hU)).toFun
  refine (isColimitOfPreserves
    (AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ))
    (SingularOpenUnion.increasingOpenChainIsColimit U hU hcover)).ofIsoColimit ?_
  exact Cocone.ext (AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X)
    (fun i => AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality (U i).inclusion')

/-- The same transport proves the colimit property for any increasing open
union, without assuming it is the whole ambient space. -/
def rationalOpenUnionChainIsColimit : IsColimit (rationalOpenUnionChainCocone U hU) := by
  apply (IsColimit.precomposeHomEquiv (rationalIncreasingOpenChainDiagramIso U hU)
    (rationalOpenUnionChainCocone U hU)).toFun
  refine (isColimitOfPreserves
    (AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ))
    (SingularOpenUnion.openUnionChainIsColimit U hU)).ofIsoColimit ?_
  exact Cocone.ext (AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso (TopCat.of (⨆ i, U i : Opens X)))
    (fun i => AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality (SingularOpenUnion.openUnionStageInclusion U i))

/-- Canonical chain-complex comparison for a full increasing open cover. -/
def rationalIncreasingOpenChainColimitIso (hcover : (⨆ i, U i) = ⊤) :
    colimit (rationalIncreasingOpenChainDiagram U hU) ≅ Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (rationalIncreasingOpenChainIsColimit U hU hcover)

@[reassoc (attr := simp)]
theorem rationalIncreasingOpenChainColimitIso_ι (hcover : (⨆ i, U i) = ⊤) (i : ℕ) :
    colimit.ι (rationalIncreasingOpenChainDiagram U hU) i ≫
        (rationalIncreasingOpenChainColimitIso U hU hcover).hom =
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (U i).inclusion' :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ i

/-- Canonical rational chain-complex comparison for the actual open union. -/
def rationalOpenUnionChainColimitIso :
    colimit (rationalIncreasingOpenChainDiagram U hU) ≅
      Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (⨆ i, U i : Opens X)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (rationalOpenUnionChainIsColimit U hU)

@[reassoc (attr := simp)]
theorem rationalOpenUnionChainColimitIso_ι (i : ℕ) :
    colimit.ι (rationalIncreasingOpenChainDiagram U hU) i ≫
        (rationalOpenUnionChainColimitIso U hU).hom =
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (SingularOpenUnion.openUnionStageInclusion U i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ i

/-- Every degree of the union comparison preserves the actual included chain. -/
theorem rationalOpenUnionChainColimitIso_degree (i n : ℕ)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U i))).X n) :
    (rationalOpenUnionChainColimitIso U hU).hom.f n
        ((colimit.ι (rationalIncreasingOpenChainDiagram U hU) i).f n z) =
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (SingularOpenUnion.openUnionStageInclusion U i)).f n z :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (rationalOpenUnionChainColimitIso_ι U hU i) n) z

/-- The ambient ordinary-homology cocone is obtained by the actual homology functor. -/
def rationalIncreasingOpenHomologyCocone (n : ℕ) :
    Cocone (rationalIncreasingOpenHomologyDiagram U hU n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapCocone
    (rationalIncreasingOpenChainCocone U hU)

/-- The union homology cocone likewise consists of the exact inclusion-induced maps. -/
def rationalOpenUnionHomologyCocone (n : ℕ) :
    Cocone (rationalIncreasingOpenHomologyDiagram U hU n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapCocone
    (rationalOpenUnionChainCocone U hU)

/-- Exactness of filtered module colimits carries the full-cover chain
colimit to the actual ordinary rational homology colimit. -/
def rationalIncreasingOpenHomologyIsColimit (hcover : (⨆ i, U i) = ⊤) (n : ℕ) :
    IsColimit (rationalIncreasingOpenHomologyCocone U hU n) :=
  isColimitOfPreserves
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n)
    (rationalIncreasingOpenChainIsColimit U hU hcover)

/-- Ordinary rational homology commutes with the actual increasing open union. -/
def rationalOpenUnionHomologyIsColimit (n : ℕ) :
    IsColimit (rationalOpenUnionHomologyCocone U hU n) :=
  isColimitOfPreserves
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n)
    (rationalOpenUnionChainIsColimit U hU)

/-- The actual rational homology comparison for a full increasing open cover. -/
def rationalIncreasingOpenHomologyColimitIso (hcover : (⨆ i, U i) = ⊤) (n : ℕ) :
    colimit (rationalIncreasingOpenHomologyDiagram U hU n) ≅
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (rationalIncreasingOpenHomologyIsColimit U hU hcover n)

@[reassoc (attr := simp)]
theorem rationalIncreasingOpenHomologyColimitIso_ι
    (hcover : (⨆ i, U i) = ⊤) (n i : ℕ) :
    colimit.ι (rationalIncreasingOpenHomologyDiagram U hU n) i ≫
        (rationalIncreasingOpenHomologyColimitIso U hU hcover n).hom =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (U i).inclusion' n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ i

/-- The rational homology comparison on the actual open union, with the
same index diagram as the canonical compact-support cap transformation. -/
def rationalOpenUnionHomologyColimitIso (n : ℕ) :
    colimit (rationalIncreasingOpenHomologyDiagram U hU n) ≅
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (⨆ i, U i : Opens X))).homology n :=
  (colimit.isColimit _).coconePointUniqueUpToIso (rationalOpenUnionHomologyIsColimit U hU n)

@[reassoc (attr := simp)]
theorem rationalOpenUnionHomologyColimitIso_ι (n i : ℕ) :
    colimit.ι (rationalIncreasingOpenHomologyDiagram U hU n) i ≫
        (rationalOpenUnionHomologyColimitIso U hU n).hom =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (SingularOpenUnion.openUnionStageInclusion U i) n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ i

private theorem iSup_eq_top_of_cover (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    (⨆ i, U i) = ⊤ := by
  apply top_unique
  intro x _hx
  exact Opens.mem_iSup.mpr (hcover x)

/-- Ambient-cover form using the pointwise cover condition of the matching
compact-support continuity theorem. -/
def rationalIncreasingOpenHomologyAmbientIso
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    colimit (rationalIncreasingOpenHomologyDiagram U hU n) ≅
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n :=
  rationalIncreasingOpenHomologyColimitIso U hU (iSup_eq_top_of_cover U hcover) n

@[reassoc (attr := simp)]
theorem rationalIncreasingOpenHomologyAmbientIso_ι
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n i : ℕ) :
    colimit.ι (rationalIncreasingOpenHomologyDiagram U hU n) i ≫
        (rationalIncreasingOpenHomologyAmbientIso U hU hcover n).hom =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (U i).inclusion' n :=
  rationalIncreasingOpenHomologyColimitIso_ι U hU (iSup_eq_top_of_cover U hcover) n i

end

end OAI.AlgebraicTopology.Duality.Poincare.RationalSingularOpenUnion
