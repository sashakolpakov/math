import OAI.AlgebraicGeometry.Comparison.Betti.ProductAntiDolbeaultPrimitive
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AcyclicityCriterion

/-! # Product Holomorphic Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProductHolomorphicAcyclicity.Dolbeault

noncomputable section

/-! The native holomorphic function sheaf has zero higher cohomology on
every finite product of complex lines and punctured complex lines. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] (ε : ι → Bool)

local instance : ProperSpace (ι → ℂ) := FiniteDimensional.proper ℝ (ι → ℂ)
local instance : LocallyCompactSpace (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) :=
  (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε).isOpen.locallyCompactSpace

local instance : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε))) :=
  HasExt.standard _

theorem productAntiDolbeault_sections_exactAt_succ (q : ℕ) :
    (((FlasqueBiproduct.sections (⊤ : Opens (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε))).mapHomologicalComplex (.up ℕ)).obj
      (Complex.AntiDolbeault.complexAntiDolbeaultComplex (ι → ℂ) (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε))).ExactAt (q + 1) :=
  Holomorphic.AcyclicityCriterion.Dolbeault.antiDolbeault_sections_exact_of_primitive (ι → ℂ) (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) q
    (ProductAntiDolbeaultPrimitive.product_antiDolbeault_global_primitive ε q)

theorem product_holomorphicScalarSheaf_ext_vanish (q : ℕ) :
    Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε)))
      (Holomorphic.ScalarSheaf.Dolbeault.holomorphicScalarSheaf (ι → ℂ) (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε)) (q + 1)) :=
  Holomorphic.AcyclicityCriterion.Dolbeault.holomorphicScalarSheaf_ext_vanish_of_primitives (ι → ℂ) (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε)
    (ProductAntiDolbeaultPrimitive.product_antiDolbeault_global_primitive ε) q

theorem product_holomorphicFunctionSheaf_cohomology_vanish (q : ℕ) :
    Subsingleton (Sheaf.H.{0}
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (ι → ℂ) (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε)) (q + 1)) :=
  Holomorphic.AcyclicityCriterion.Dolbeault.holomorphicFunctionSheaf_cohomology_vanish_of_primitives (ι → ℂ) (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε)
    (ProductAntiDolbeaultPrimitive.product_antiDolbeault_global_primitive ε) q

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProductHolomorphicAcyclicity.Dolbeault
