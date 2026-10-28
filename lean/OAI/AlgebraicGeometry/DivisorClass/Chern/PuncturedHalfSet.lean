import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductCharts
import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductEquator
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-! # Punctured Half Set -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PuncturedHalfSet

noncomputable section

/-!
# ChernClass: a common punctured support for the half-disk product boundary

Both kinds of product boundary pieces map into this actual punctured
subspace. Its singular-chain inclusion is injective, so chain
identities may be checked after inclusion in the full product.
-/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def puncturedHalfProductSet (m : ℕ) (b : Bool) :
    Set (PlaneHalf.coordinatePlaneHalf b × EuclideanSpace ℝ (Fin m)) :=
  {p | (p.1.val, p.2) ≠ 0}

abbrev PuncturedHalfProduct (m : ℕ) (b : Bool) := puncturedHalfProductSet m b

def halfProductPunctureInclusion (m : ℕ) (b : Bool) :
    TopCat.of (PuncturedHalfProduct m b) ⟶
      TopCat.of (PlaneHalf.coordinatePlaneHalf b × EuclideanSpace ℝ (Fin m)) :=
  CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (PlaneHalf.coordinatePlaneHalf b × EuclideanSpace ℝ (Fin m)))
    (puncturedHalfProductSet m b)

def halfProductRightMap (m : ℕ) (b : Bool) :
    TopCat.of (PlaneHalf.coordinatePlaneHalf b × CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))) ⟶
      TopCat.of (PuncturedHalfProduct m b) :=
  TopCat.ofHom ⟨fun p => ⟨(p.1, p.2.val), by
      intro h
      exact p.2.property (congrArg Prod.snd h)⟩,
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

def halfProductLeftMap (m : ℕ) (b : Bool) :
    TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b × EuclideanSpace ℝ (Fin m)) ⟶
      TopCat.of (PuncturedHalfProduct m b) :=
  TopCat.ofHom ⟨fun p => ⟨(p.1.val, p.2), by
      intro h
      exact p.1.property (congrArg Prod.fst h)⟩,
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _⟩

def halfProductChartMap (m : ℕ) (b : Bool) :
    TopCat.of (PuncturedHalfProduct m b) ⟶ TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (PlaneProductCharts.planeProductPole m b)) := by
  let v : C(PuncturedHalfProduct m b, CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (m + 2)))) :=
    ⟨fun p => ⟨PlaneProductCharts.planeProductCoordinates m (p.val.1.val, p.val.2), by
        intro h
        exact p.property ((PlaneProductCharts.planeProductCoordinates m).injective (h.trans (map_zero _).symm))⟩,
      ((PlaneProductCharts.planeProductCoordinates m).continuous.comp
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
          (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩
  exact TopCat.ofHom
    ⟨fun p => ⟨CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _ (v p),
      PlaneProductCharts.planeProduct_radial_mem_chart m b p.val.1 p.val.2 (v p).property⟩,
      ((CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _).continuous.comp v.continuous).subtype_mk _⟩

theorem halfProductRightMap_chart (m : ℕ) (b : Bool) :
    halfProductRightMap m b ≫ halfProductChartMap m b = TopCat.ofHom (PlaneProductCharts.planeHalfRightChartMap m b) := rfl

theorem halfProductLeftMap_chart (m : ℕ) (b : Bool) :
    halfProductLeftMap m b ≫ halfProductChartMap m b = TopCat.ofHom (PlaneProductCharts.planeHalfLeftChartMap m b) := rfl

theorem halfProductPuncture_chain_injective (k : Type) [Field k] (m : ℕ) (b : Bool) (n : ℕ) :
    Function.Injective (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map (halfProductPunctureInclusion m b)).f n) := by
  let X := TopCat.of (PlaneHalf.coordinatePlaneHalf b × EuclideanSpace ℝ (Fin m))
  let A : Set X := puncturedHalfProductSet m b
  have : Mono ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A).f n) :=
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_degreewiseShortExact k X A n).mono_f
  exact (ModuleCat.mono_iff_injective _).mp this

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PuncturedHalfSet
