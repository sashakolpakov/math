import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology
import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

/-! # Rationalized Chain Classes -/

namespace OAI.AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles

noncomputable section

/-!
# Explicit cycle representatives under rationalization

The native homology comparison for exact rationalization sends the actual
cycle `q ⊗ z` to `q ⊗ [z]`. This file proves that normalization from the
canonical cycle and homology projections, for every degree including zero.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

variable (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- The elementary rational tensor of an integral cycle is an actual cycle
of the degreewise rationalized complex. -/
def rationalizedChainCycle (q : ℚ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj C) n :=
  ⟨q ⊗ₜ[ℤ, Int.castRingHom ℚ] z.val, by
    change (q ⊗ₜ[ℤ, Int.castRingHom ℚ] ((C.sc n).g z.val)) = 0
    rw [show (C.sc n).g z.val = 0 from z.property, TensorProduct.tmul_zero]⟩

/-- The rationalized cycle has exactly the asserted elementary tensor as its
underlying chain. -/
@[simp]
theorem rationalizedChainCycle_val (q : ℚ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    (rationalizedChainCycle C n q z).val = q ⊗ₜ[ℤ, Int.castRingHom ℚ] z.val := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical rationalization isomorphisms commute with the native
projection from cycles to homology. -/
@[reassoc]
theorem rationalizeHomologyIso_homologyπ :
    (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj C).homologyπ n ≫ (AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeHomologyIso C n).hom =
      ((C.sc n).mapCyclesIso AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules).hom ≫
        AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (C.homologyπ n) := by
  let S := C.sc n
  change (S.map AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules).homologyπ ≫
      (S.mapHomologyIso AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules).hom =
    (S.mapCyclesIso AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules).hom ≫ AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map S.homologyπ
  rw [S.leftHomologyData.mapHomologyIso_eq AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules,
    S.leftHomologyData.mapCyclesIso_eq AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  simp only [Category.assoc, ShortComplex.LeftHomologyData.map_π]
  rw [← AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map_comp, S.leftHomologyData.π_comp_homologyIso_inv,
    AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The native comparison on cycles sends the elementary rationalized cycle
to the elementary tensor of the native integral cycle. -/
theorem rationalizedChainCycle_mapCyclesIso (q : ℚ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    ((C.sc n).mapCyclesIso AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules).hom
        (((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj C).sc n).moduleCatCyclesIso.inv
          (rationalizedChainCycle C n q z)) =
      q ⊗ₜ[ℤ, Int.castRingHom ℚ] ((C.sc n).moduleCatCyclesIso.inv z) := by
  apply (ModuleCat.mono_iff_injective (AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (C.sc n).iCycles)).mp
    inferInstance
  calc
    _ = ((C.sc n).map AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules).iCycles
        (((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj C).sc n).moduleCatCyclesIso.inv
          (rationalizedChainCycle C n q z)) :=
      ConcreteCategory.congr_hom ((C.sc n).mapCyclesIso_hom_iCycles AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules) _
    _ = q ⊗ₜ[ℤ, Int.castRingHom ℚ] z.val :=
      ConcreteCategory.congr_hom
        (((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj C).sc n).moduleCatCyclesIso_inv_iCycles)
        (rationalizedChainCycle C n q z)
    _ = _ := by
      change (q ⊗ₜ[ℤ, Int.castRingHom ℚ] z.val) =
        q ⊗ₜ[ℤ, Int.castRingHom ℚ]
          ((C.sc n).iCycles ((C.sc n).moduleCatCyclesIso.inv z))
      have hi := ConcreteCategory.congr_hom ((C.sc n).moduleCatCyclesIso_inv_iCycles) z
      change (C.sc n).iCycles ((C.sc n).moduleCatCyclesIso.inv z) = z.val at hi
      exact congrArg (fun w => q ⊗ₜ[ℤ, Int.castRingHom ℚ] w)
        hi.symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical native homology comparison sends `[q ⊗ z]` to `q ⊗ [z]`.
No scalar or sign ambiguity remains in this representative formula. -/
@[simp]
theorem rationalizeHomologyIso_chainClass (q : ℚ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    (AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeHomologyIso C n).hom
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj C) n
          (rationalizedChainCycle C n q z)) =
      q ⊗ₜ[ℤ, Int.castRingHom ℚ] (Cohomology.Singular.ChainRepresentatives.chainClass C n z) := by
  rw [Cohomology.Singular.ChainRepresentatives.chainClass_eq_homologyπ, Cohomology.Singular.ChainRepresentatives.chainClass_eq_homologyπ]
  calc
    _ = AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (C.homologyπ n)
        (((C.sc n).mapCyclesIso AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules).hom
          (((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj C).sc n).moduleCatCyclesIso.inv
            (rationalizedChainCycle C n q z))) :=
      ConcreteCategory.congr_hom (rationalizeHomologyIso_homologyπ C n) _
    _ = AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (C.homologyπ n)
        (q ⊗ₜ[ℤ, Int.castRingHom ℚ] ((C.sc n).moduleCatCyclesIso.inv z)) := by
      rw [rationalizedChainCycle_mapCyclesIso]
    _ = _ := rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles
