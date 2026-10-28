import OAI.AlgebraicGeometry.Divisors.LineBundles.FiberFundamentalCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint

/-! # Fiber Fundamental Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFundamentalCycle.BundleCycles

noncomputable section

/-! For an integral fiber the actual fundamental cycle consists of its
unique generic point with local-ring length one. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem componentGenericPoint_eq_genericPoint (X : Scheme.{0}) [IsIntegral X]
    (C : irreducibleComponents X) : FiberFundamentalCycle.BundleCycles.componentGenericPoint X C = genericPoint X := by
  have hC : C.val = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using C.property
  let W : IrreducibleCloseds X := ⟨C.val, C.property.1, isClosed_of_mem_irreducibleComponents _ C.property⟩
  have h : IsGenericPoint (FiberFundamentalCycle.BundleCycles.componentGenericPoint X C) C.val := W.isIrreducible.isGenericPoint_genericPoint W.isClosed
  rw [hC] at h
  exact h.eq (genericPoint_spec X)

theorem componentGenericPoint_length_one (X : Scheme.{0}) [IsIntegral X]
    (C : irreducibleComponents X) :
    Module.length (X.presheaf.stalk (FiberFundamentalCycle.BundleCycles.componentGenericPoint X C))
      (X.presheaf.stalk (FiberFundamentalCycle.BundleCycles.componentGenericPoint X C)) = 1 := by
  rw [componentGenericPoint_eq_genericPoint]
  change Module.length X.functionField X.functionField = 1
  exact Module.length_eq_one _ _

variable {X Y : Scheme.{0}} (p : X ⟶ Y) [LocallyOfFiniteType p] [QuasiCompact p] [GeometricallyIntegral p]

theorem integralFiber_fundamentalPointCycle (y : Y) :
    FiberFundamentalCycle.BundleCycles.fiberFundamentalPointCycle p y = Finsupp.single (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p y) 1 := by
  classical
  let Z := p.fiber y
  let C : irreducibleComponents Z := ⟨Set.univ, by simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]⟩
  let : Unique (irreducibleComponents Z) := ⟨⟨C⟩, fun D => Subtype.ext (by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using D.property)⟩
  let := (NoetherianSpace.finite_irreducibleComponents (α := Z)).fintype
  change (∑ D : irreducibleComponents Z, Finsupp.single (p.fiberι y (FiberFundamentalCycle.BundleCycles.componentGenericPoint Z D))
    ((Module.length (Z.presheaf.stalk (FiberFundamentalCycle.BundleCycles.componentGenericPoint Z D))
      (Z.presheaf.stalk (FiberFundamentalCycle.BundleCycles.componentGenericPoint Z D))).toNat : ℚ)) = _
  apply (Fintype.sum_unique _).trans
  have hp := congrArg (p.fiberι y) (componentGenericPoint_eq_genericPoint Z (default : irreducibleComponents Z))
  have hl := congrArg (fun n : ℕ∞ => (n.toNat : ℚ))
    (componentGenericPoint_length_one Z (default : irreducibleComponents Z))
  exact congrArg₂ Finsupp.single hp hl

theorem fiberPointCyclePullback_eq_integralFiberCycleExtension :
    FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback p = FiberGenericPoint.BundleCycles.integralFiberCycleExtension p := by
  apply Finsupp.lhom_ext
  intro y a
  rw [FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback_single, integralFiber_fundamentalPointCycle]
  change a • Finsupp.single (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p y) 1 =
    Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) (Finsupp.single y a)
  rw [Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFundamentalCycle.BundleCycles
