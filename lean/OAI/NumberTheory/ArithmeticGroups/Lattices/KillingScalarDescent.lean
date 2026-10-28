import OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricLieSemisimple
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.ScalarEquiv

/-! # Killing Scalar Descent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.KillingScalarDescent.Construction

noncomputable section

/-! Nondegeneracy of the Killing form descends along field extensions.
In particular, the original rational infinitesimal Lie algebra of an
Lattices semisimple group is semisimple. -/

open scoped Classical TensorProduct

theorem isKilling_of_scalar_extension
    {k K L : Type*} [Field k] [Field K] [Algebra k K]
    [LieRing L] [LieAlgebra k L] [Module.Finite k L]
    [LieAlgebra.IsKilling K (K ⊗[k] L)] : LieAlgebra.IsKilling k L := by
  constructor
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  have hxy : ∀ y : L, killingForm k L x y = 0 := by
    intro y
    rw [LieModule.traceForm_comm]
    exact hx y (LieSubmodule.mem_top y)
  have hker : (1 : K) ⊗ₜ[k] x ∈ LinearMap.ker (killingForm K (K ⊗[k] L)) := by
    change killingForm K (K ⊗[k] L) (1 ⊗ₜ[k] x) = 0
    apply LinearMap.ext
    intro y
    change LieModule.traceForm K (K ⊗[k] L) (K ⊗[k] L) (1 ⊗ₜ[k] x) y = 0
    rw [LieModule.traceForm_baseChange]
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, hy, hz, add_zero]
    | tmul a y =>
      rw [LinearMap.BilinForm.baseChange_tmul]
      change killingForm k L x y • (1 * a) = 0
      rw [hxy, zero_smul]
  have hz : (1 : K) ⊗ₜ[k] x = 0 := by
    simpa only [LieAlgebra.IsKilling.ker_killingForm_eq_bot, Submodule.mem_bot] using hker
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff k L x).mp hz

attribute [local instance] LieRing.ofAssociativeRing

theorem infinitesimal_isKilling
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    LieAlgebra.IsKilling k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) := by
  let : LieAlgebra.IsSemisimple (AlgebraicClosure k)
      (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k)))) :=
    GeometricLieSemisimple.Construction.geometric_infinitesimal_isSemisimple G hsemi
  let : LieAlgebra.IsKilling (AlgebraicClosure k)
      (AlgebraicClosure k ⊗[k] Infinitesimal.Action.Construction.infinitesimalStabilizer G) :=
    (Infinitesimal.ScalarEquiv.Construction.infinitesimalScalarLieEquiv (K := AlgebraicClosure k) G hconn).symm.isKilling
  exact isKilling_of_scalar_extension (K := AlgebraicClosure k)

theorem infinitesimal_isSemisimple
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    LieAlgebra.IsSemisimple k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) := by
  let : LieAlgebra.IsKilling k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) := infinitesimal_isKilling G hconn hsemi
  infer_instance

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.KillingScalarDescent.Construction
