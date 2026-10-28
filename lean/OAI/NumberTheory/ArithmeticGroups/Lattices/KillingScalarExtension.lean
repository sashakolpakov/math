import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingScalarDescent

/-! # Killing Scalar Extension -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.KillingScalarExtension.Construction

noncomputable section

/-! Nondegenerate finite-dimensional bilinear forms and Killing Lie
algebras remain nondegenerate under scalar extension. -/

open scoped Classical TensorProduct

theorem bilinear_nondegenerate_baseChange
    {k K V : Type*} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate) : (B.baseChange K).Nondegenerate := by
  let b := Module.finBasis k V
  have he : LinearMap.BilinForm.toMatrix (b.baseChange K) (B.baseChange K) =
      (algebraMap k K).mapMatrix (LinearMap.BilinForm.toMatrix b B) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
      LinearMap.BilinForm.baseChange_tmul, one_mul]
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply]
    rw [Algebra.smul_def, mul_one]
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange K), he, ← RingHom.map_det]
  exact (map_ne_zero (algebraMap k K)).mpr (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b |>.mp hB)

theorem isKilling_scalar_extension
    {k K L : Type*} [Field k] [Field K] [Algebra k K]
    [LieRing L] [LieAlgebra k L] [Module.Finite k L] [LieAlgebra.IsKilling k L] :
    LieAlgebra.IsKilling K (K ⊗[k] L) := by
  have hB : (killingForm K (K ⊗[k] L)).Nondegenerate := by
    change (LieModule.traceForm K (K ⊗[k] L) (K ⊗[k] L)).Nondegenerate
    rw [LieModule.traceForm_baseChange]
    exact bilinear_nondegenerate_baseChange (killingForm k L) (LieAlgebra.IsKilling.killingForm_nondegenerate k L)
  constructor
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  exact hB.2 x (fun y => hx y (LieSubmodule.mem_top y))

attribute [local instance] LieRing.ofAssociativeRing

theorem infinitesimal_baseChange_isKilling
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    LieAlgebra.IsKilling K (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) := by
  let : LieAlgebra.IsKilling k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) := KillingScalarDescent.Construction.infinitesimal_isKilling G hconn hsemi
  let : LieAlgebra.IsKilling K (K ⊗[k] Infinitesimal.Action.Construction.infinitesimalStabilizer G) := isKilling_scalar_extension
  exact (Infinitesimal.ScalarEquiv.Construction.infinitesimalScalarLieEquiv G hconn).isKilling

theorem infinitesimal_baseChange_isSemisimple
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    LieAlgebra.IsSemisimple K (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) := by
  let : LieAlgebra.IsKilling K (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) :=
    infinitesimal_baseChange_isKilling G hconn hsemi
  infer_instance

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.KillingScalarExtension.Construction
