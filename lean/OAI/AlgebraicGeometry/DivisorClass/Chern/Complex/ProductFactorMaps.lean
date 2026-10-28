import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.DiskProductGenerator
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.DiskGenerator

/-! # Product Factor Maps -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ProductFactorMaps

noncomputable section

/-! The factorwise maps of the actual fillings and their literal complex
concatenation are the already normalized total coordinate map. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def complexProductFactorMap (p : ℕ) :
    TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin (2 * p + 2))) ⟶
      TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ)) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((DiskGenerator.planeToNormalLine, Positive.ComplexCoordinates.positiveEuclideanToComplex p) :
    (TopCat.of PlaneHalf.CoordinatePlane, TopCat.of (EuclideanSpace ℝ (Fin (2 * p + 2)))) ⟶
    (TopCat.of (Fin 1 → ℂ), TopCat.of (Fin (p + 1) → ℂ)))

theorem complexProductFactorMap_puncture (p : ℕ) :
    Set.MapsTo (complexProductFactorMap p) ({0}ᶜ)
      ({0}ᶜ : Set ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) := by
  intro x hx he
  let e := ((CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1).symm).prodCongr (Positive.ComplexCoordinates.positiveComplexRealCoordinates p).symm
  exact hx (e.injective (he.trans (map_zero e).symm))

def complexProductLineMap (p : ℕ) :
    TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ)) ⟶ TopCat.of (Fin (p + 2) → ℂ) :=
  TopCat.ofHom ⟨LineProductCoordinates.complexLineProductCoordinates (p + 1), (LineProductCoordinates.complexLineProductCoordinates (p + 1)).continuous⟩

theorem complexProductLineMap_puncture (p : ℕ) :
    Set.MapsTo (complexProductLineMap p) ({0}ᶜ) ({0}ᶜ : Set (Fin (p + 2) → ℂ)) := by
  intro x hx he
  exact hx ((LineProductCoordinates.complexLineProductCoordinates (p + 1)).injective
    (he.trans (map_zero (LineProductCoordinates.complexLineProductCoordinates (p + 1))).symm))

theorem complexProductFactorMap_comp_line (p : ℕ) :
    complexProductFactorMap p ≫ complexProductLineMap p = DiskProductGenerator.fullPlaneProductComplexMap p := rfl

theorem normalSupportedDiskRationalFilling_of_plane :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map DiskGenerator.planeToNormalLine).f 2 PlaneProductTo.rationalPlaneDiskFilling =
      Rational.DiskGenerator.normalSupportedDiskRationalFilling := by
  rw [PlaneProductTo.rationalPlaneDiskFilling, Rational.ChainRepresentatives.rationalSingularChainElement_map]
  rfl

theorem positiveComplexRationalFilling_of_euclidean (p : ℕ) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Positive.ComplexCoordinates.positiveEuclideanToComplex p)).f (2 * p + 2)
      (DiskProductSphereGenerator.euclideanOrthantRationalFilling (2 * p)) = Rational.PositiveComplexSphere.positiveComplexRationalFilling p := by
  rw [DiskProductSphereGenerator.euclideanOrthantRationalFilling, Rational.ChainRepresentatives.rationalSingularChainElement_map]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ProductFactorMaps
