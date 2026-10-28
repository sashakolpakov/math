import OAI.Topology.Euclidean.ProductComplexes
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.LinearAlgebra.Pi

/-! # Indexed Product -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.IndexedProduct

noncomputable section

/-!
# Cohomology of indexed products of module complexes

The actual Cartesian product functor preserves homology. The resulting
canonical equivalence below is characterized by the cohomology maps induced
by the component projections.
-/

open _root_.CategoryTheory
open OAI.Topology.Euclidean.ProductComplexes.Globalization

variable (R : Type) [Ring R] (I : Type)

/-- The coordinate projection of the actual module-product functor. -/
def moduleIndexedProjection (i : I) :
    Topology.Euclidean.ProductComplexes.Globalization.moduleIndexedProduct R I ⟶ (evaluation (Discrete I) (ModuleCat.{0} R)).obj ⟨i⟩ where
  app F := ModuleCat.ofHom (LinearMap.proj i)
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

variable {I}

/-- The actual projection from the Cartesian product complex to a component. -/
def indexedProductProjection (K : I → CochainComplex (ModuleCat.{0} R) ℕ) (i : I) :
    Topology.Euclidean.ProductComplexes.Globalization.indexedProductComplex R K ⟶ K i :=
  ((moduleIndexedProjection R I i).mapHomologicalComplex (ComplexShape.up ℕ)).app
    (Topology.Euclidean.ProductComplexes.Globalization.cochainIndexedFamily R K)

@[simp]
theorem indexedProductProjection_f_apply (K : I → CochainComplex (ModuleCat.{0} R) ℕ)
    (i : I) (n : ℕ) (x : (Topology.Euclidean.ProductComplexes.Globalization.indexedProductComplex R K).X n) :
    (indexedProductProjection R K i).f n x = x i := rfl

/-- Cohomology of the actual product complex is the product of the component
cohomology modules. -/
def indexedProductCohomologyEquiv (K : I → CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (Topology.Euclidean.ProductComplexes.Globalization.indexedProductComplex R K).homology n ≃ₗ[R] (∀ i, (K i).homology n) :=
  (((Topology.Euclidean.ProductComplexes.Globalization.cochainIndexedFamily R K).sc n).mapHomologyIso (Topology.Euclidean.ProductComplexes.Globalization.moduleIndexedProduct R I)).toLinearEquiv.trans
    (LinearEquiv.piCongrRight fun i =>
      (((Topology.Euclidean.ProductComplexes.Globalization.cochainIndexedFamily R K).sc n).mapHomologyIso
        ((evaluation (Discrete I) (ModuleCat.{0} R)).obj ⟨i⟩)).symm.toLinearEquiv)

/-- The canonical cohomology equivalence sends a class to its images under
the actual component projections. -/
theorem indexedProductCohomologyEquiv_apply
    (K : I → CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (c : (Topology.Euclidean.ProductComplexes.Globalization.indexedProductComplex R K).homology n) (i : I) :
    indexedProductCohomologyEquiv R K n c i =
      HomologicalComplex.homologyMap (indexedProductProjection R K i) n c := by
  exact (ConcreteCategory.congr_hom
    (((Topology.Euclidean.ProductComplexes.Globalization.cochainIndexedFamily R K).sc n).homologyMap_mapNatTrans
      (moduleIndexedProjection R I i)) c).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.IndexedProduct
