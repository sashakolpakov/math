import OAI.NumberTheory.ArithmeticGroups.Lattices.TraceRestriction
import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingScalarDescent

/-! # Killing Restriction -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.KillingRestriction.Construction

noncomputable section

/-! A Killing Lie algebra stays Killing when scalars are restricted
through a finite separable field extension. -/

open scoped Classical
open LieAlgebra

theorem killingForm_restrictScalars
    {k K L : Type*} [Field k] [Field K] [Algebra k K]
    [LieRing L] [LieAlgebra k L] [LieAlgebra K L] [IsScalarTower k K L]
    [Module.Finite k K] [Module.Finite K L] (x y : L) :
    killingForm k L x y = Algebra.trace k K (killingForm K L x y) := by
  have he : (ad k L x).comp (ad k L y) = ((ad K L x).comp (ad K L y)).restrictScalars k := by
    apply LinearMap.ext
    intro z
    rfl
  rw [killingForm_apply_apply, killingForm_apply_apply, he, TraceRestriction.Construction.linear_trace_restrictScalars]

theorem isKilling_restrictScalars
    {k K L : Type*} [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    [LieRing L] [LieAlgebra k L] [LieAlgebra K L] [IsScalarTower k K L]
    [Module.Finite k K] [Module.Finite K L] [LieAlgebra.IsKilling K L] :
    LieAlgebra.IsKilling k L := by
  constructor
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply (LieAlgebra.IsKilling.killingForm_nondegenerate K L).2 x
  intro y
  apply (traceForm_nondegenerate k K).1 (killingForm K L y x)
  intro a
  have ha := hx (a • y) (LieSubmodule.mem_top _)
  rw [killingForm_restrictScalars (k := k) (K := K)] at ha
  change Algebra.trace k K (killingForm K L (a • y) x) = 0 at ha
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at ha
  change Algebra.trace k K (killingForm K L y x * a) = 0
  rwa [mul_comm]

attribute [local instance] LieRing.ofAssociativeRing

@[instance_reducible] def infinitesimalRationalLieAlgebra
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : LieAlgebra ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G) where
  toModule := inferInstance
  lie_smul r x y := by
    apply Subtype.ext
    change x.val * (r • y.val) - (r • y.val) * x.val = r • (x.val * y.val - y.val * x.val)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

attribute [local instance] infinitesimalRationalLieAlgebra

theorem infinitesimal_rational_isKilling
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (hsemi : G.IsSemisimple) : LieAlgebra.IsKilling ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G) := by
  let : LieAlgebra.IsKilling k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) := KillingScalarDescent.Construction.infinitesimal_isKilling G hG hsemi
  exact isKilling_restrictScalars (K := k)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.KillingRestriction.Construction
