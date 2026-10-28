import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.TangentExtension

/-! # Scalar Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.ScalarEquiv.Construction

noncomputable section

/-! The scalar-extension isomorphism for the concrete infinitesimal Lie
algebra, including compatibility with the Lie bracket. -/

open scoped Classical TensorProduct

attribute [local instance] LieRing.ofAssociativeRing

def infinitesimalScalarMap
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) :
    K ⊗[k] Action.Construction.infinitesimalStabilizer G →ₗ[K] Matrix (Fin n) (Fin n) K :=
  (MatrixFlatExtension.Construction.matrixScalarExtension n).toLinearMap.comp
    ((Action.Construction.infinitesimalStabilizer G).toSubmodule.subtype.baseChange K)

theorem infinitesimalScalarMap_tmul
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (a : K) (A : Action.Construction.infinitesimalStabilizer G) :
    infinitesimalScalarMap G (a ⊗ₜ[k] A) = a • A.val.map (algebraMap k K) := by
  change MatrixFlatExtension.Construction.matrixScalarExtension n
    ((Action.Construction.infinitesimalStabilizer G).toSubmodule.subtype.baseChange K (a ⊗ₜ[k] A)) = _
  rw [LinearMap.baseChange_tmul, MatrixFlatExtension.Construction.matrixScalarExtension_tmul]
  rfl

theorem infinitesimalScalarMap_injective
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : Function.Injective (infinitesimalScalarMap (K := K) G) :=
  (MatrixFlatExtension.Construction.matrixScalarExtension n).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap
      (Action.Construction.infinitesimalStabilizer G).toSubmodule.subtype Subtype.val_injective)

theorem infinitesimalScalarMap_range
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    (infinitesimalScalarMap (K := K) G).range =
      (Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule := by
  rw [← TangentExtension.Construction.infinitesimalStabilizer_baseChange G hG]
  exact LinearMap.range_comp _ _

def infinitesimalScalarLinearEquiv
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    K ⊗[k] Action.Construction.infinitesimalStabilizer G ≃ₗ[K]
      Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) :=
  (LinearEquiv.ofInjective (infinitesimalScalarMap G) (infinitesimalScalarMap_injective G)).trans
    (LinearEquiv.ofEq _ _ (infinitesimalScalarMap_range G hG))

theorem infinitesimalScalarLinearEquiv_coe
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (x : K ⊗[k] Action.Construction.infinitesimalStabilizer G) :
    (infinitesimalScalarLinearEquiv G hG x).val = infinitesimalScalarMap G x := rfl

theorem infinitesimalScalarMap_lie
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (x y : K ⊗[k] Action.Construction.infinitesimalStabilizer G) :
    infinitesimalScalarMap G ⁅x, y⁆ = ⁅infinitesimalScalarMap G x, infinitesimalScalarMap G y⁆ := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [add_lie, map_add, hx, hz]
  | tmul a A =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz =>
          have hadd : ⁅(a ⊗ₜ[k] A : K ⊗[k] Action.Construction.infinitesimalStabilizer G), y + z⁆ =
              ⁅a ⊗ₜ[k] A, y⁆ + ⁅a ⊗ₜ[k] A, z⁆ := LieRing.lie_add _ _ _
          rw [hadd, map_add, hy, hz, map_add, lie_add]
      | tmul b B =>
          rw [LieAlgebra.ExtendScalars.bracket_tmul, infinitesimalScalarMap_tmul,
            infinitesimalScalarMap_tmul, infinitesimalScalarMap_tmul, smul_lie, lie_smul, smul_smul]
          congr 1
          change (algebraMap k K).mapMatrix ⁅A.val, B.val⁆ =
            ⁅(algebraMap k K).mapMatrix A.val, (algebraMap k K).mapMatrix B.val⁆
          simp only [Ring.lie_def, map_sub, map_mul]

def infinitesimalScalarLieEquiv
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    K ⊗[k] Action.Construction.infinitesimalStabilizer G ≃ₗ⁅K⁆
      Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) :=
  { infinitesimalScalarLinearEquiv G hG with
    map_lie' := by
      intro x y
      apply Subtype.ext
      exact infinitesimalScalarMap_lie G x y }

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.ScalarEquiv.Construction
