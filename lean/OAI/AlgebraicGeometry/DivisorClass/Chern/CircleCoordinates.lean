import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleArcWinding
import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyZeroNaturality

/-! # Circle Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CircleCoordinates

noncomputable section

/-! Actual point-chain classes in the zero-sphere coordinates used by Mayer–Vietoris. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyZeroNaturality.Cycles
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def integralPointClass (X : TopCat.{0}) (x : X) : CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomology X 0 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) 0 ⟨CircleArcWinding.integralPointChain X x, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _⟩

/-- The explicit point-chain class is the native singular H0 generator. -/
theorem integralPointClass_eq_generator (X : TopCat.{0}) (x : X) :
    integralPointClass X x = CycleClass.Geometric.HomologyZeroNaturality.Cycles.simplicialH0Generator (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ)
      ((TopCat.toSSetObj₀Equiv (X := X)).symm x) 1 := by
  let C := CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X
  let s := (TopCat.toSSetObj₀Equiv (X := X)).symm x
  let lift : ModuleCat.of ℤ ℤ ⟶ C.cycles 0 :=
    C.liftCycles ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s) 0 (by simp) (by simp)
  have hcycle : (C.sc 0).moduleCatCyclesIso.inv
      ⟨CircleArcWinding.integralPointChain X x, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero C _⟩ = lift 1 := by
    apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
    have hleft := ConcreteCategory.congr_hom ((C.sc 0).moduleCatCyclesIso_inv_iCycles)
      ⟨CircleArcWinding.integralPointChain X x, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero C _⟩
    have hright := ConcreteCategory.congr_hom
      (C.liftCycles_i ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s)
        0 (by simp) (by simp)) (1 : ℤ)
    exact hleft.trans hright.symm
  change AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C 0 _ = _
  rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_homologyπ, hcycle]
  rfl

/-- Continuous maps preserve these actual point classes. -/
theorem integralPointClass_map {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap f 0 (integralPointClass X x) = integralPointClass Y (f x) := by
  rw [integralPointClass_eq_generator, integralPointClass_eq_generator]
  exact ConcreteCategory.congr_hom (CycleClass.Geometric.HomologyZeroNaturality.Cycles.simplicialH0Generator_naturality (TopCat.toSSet.map f)
    (ModuleCat.of ℤ ℤ) ((TopCat.toSSetObj₀Equiv (X := X)).symm x)) 1

/-- The original zero-sphere coordinate assigns a point chain its literal label. -/
theorem zeroSphereCoordinates_pointChain (i : Fin 2) :
    CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereCoordinates (integralPointClass CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere i) = Pi.single i 1 := by
  rw [integralPointClass_eq_generator]
  have h : CycleClass.Geometric.HomologyZeroNaturality.Cycles.simplicialH0Generator (TopCat.toSSet.obj CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere) (ModuleCat.of ℤ ℤ)
      ((TopCat.toSSetObj₀Equiv (X := CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere)).symm i) ≫ CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereH0Iso.hom =
    Sigma.ι (fun _ : Fin 2 => ModuleCat.of ℤ ℤ) i ≫ CycleClass.Geometric.ZeroSphere.Cycles.twoIntegerCoproductIso.hom := by
    have hzero := (TopCat.toSSet.obj CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere).liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
      (ModuleCat.of ℤ ℤ) ((TopCat.toSSetObj₀Equiv (X := CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere)).symm i)
    change CycleClass.Geometric.HomologyZeroNaturality.Cycles.simplicialH0Generator (TopCat.toSSet.obj CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere) (ModuleCat.of ℤ ℤ)
        ((TopCat.toSSetObj₀Equiv (X := CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere)).symm i) ≫
        ((TopCat.toSSet.obj CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere).homology₀Iso (ModuleCat.of ℤ ℤ)).hom = _ at hzero
    change (_ ≫ ((TopCat.toSSet.obj CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere).homology₀Iso (ModuleCat.of ℤ ℤ)).hom) ≫
      CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereComponentCoproductIso.hom ≫ CycleClass.Geometric.ZeroSphere.Cycles.twoIntegerCoproductIso.hom = _
    rw [hzero]
    simp only [CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereComponentCoproductIso, sigmaConst, Functor.mapIso_hom]
    simp
    exact congrArg (fun j : Fin 2 => Sigma.ι (fun _ : Fin 2 => ModuleCat.of ℤ ℤ) j)
      (CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereComponentEquiv_mk i)
  exact (ConcreteCategory.congr_hom h (1 : ℤ)).trans (CycleClass.Geometric.ZeroSphere.Cycles.twoIntegerCoproductIso_ι_apply i 1)

/-- The original overlap homology map sends a point to its actual zero-sphere label. -/
theorem circleOverlapH0_pointClass (x : CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap) :
    CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereCoordinates (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapH0Equiv (integralPointClass CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap x)) =
      Pi.single (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv x) 1 := by
  have h := integralPointClass_map (TopCat.ofHom CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv.toFun) x
  change CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapH0Equiv (integralPointClass CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap x) =
    integralPointClass CycleClass.Geometric.ZeroSphere.Cycles.zeroSphere (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv x) at h
  rw [h, zeroSphereCoordinates_pointChain]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CircleCoordinates
