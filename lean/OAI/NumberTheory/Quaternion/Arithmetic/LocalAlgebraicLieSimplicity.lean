import OAI.NumberTheory.Quaternion.Arithmetic.GeometricLieSimplicity
import OAI.NumberTheory.Quaternion.Arithmetic.SimpleLie
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.ScalarEquiv

/-! # Local Algebraic Lie Simplicity -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalAlgebraicLieSimplicity

noncomputable section

/-! The infinitesimal Lie algebra of an absolutely almost-simple
semisimple group is simple over every extension field. Geometric
simplicity extends to a common algebraic closure and then descends. -/

open scoped Classical TensorProduct
open OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.ScalarEquiv.Construction

attribute [local instance] LieRing.ofAssociativeRing

variable {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}

theorem infinitesimal_simple_over_algClosed_extension [IsAlgClosed K]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple) :
    LieAlgebra.IsSimple K (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) := by
  let ι : AlgebraicClosure k →ₐ[k] K := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure k) K := ι.toRingHom.toAlgebra
  let : IsScalarTower k (AlgebraicClosure k) K :=
    IsScalarTower.of_algebraMap_eq (fun a => (ι.commutes a).symm)
  let H := ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))
  have hH : H.IsGeometricallyConnected := ArithmeticGroups.Lattices.ConnectedBaseChange.Construction.geometrically_connected_baseChange G hsimple.1
  let : LieAlgebra.IsSimple (AlgebraicClosure k) (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H) :=
    GeometricLieSimplicity.geometric_infinitesimal_isSimple G hsimple hsemi
  let : LieAlgebra.IsSimple K (K ⊗[AlgebraicClosure k] ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H) :=
    SimpleLie.simple_lie_baseChange_of_algClosed
  have h := SimpleLie.simple_of_LieEquiv (ArithmeticGroups.Lattices.Infinitesimal.ScalarEquiv.Construction.infinitesimalScalarLieEquiv (K := K) H hH)
  have he : ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange H (algebraMap (AlgebraicClosure k) K) =
      ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K) := by
    dsimp only [H]
    rw [ArithmeticGroups.Lattices.ConnectedBaseChange.Construction.matrixGroupBaseChange_trans]
    congr 1
    ext a
    exact ι.commutes a
  rw [he] at h
  exact h

theorem infinitesimal_simple_over_extension
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple) :
    LieAlgebra.IsSimple K (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) := by
  let Ω := AlgebraicClosure K
  let : CharZero K := Algebra.charZero_of_charZero k K
  let H := ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)
  have hH : H.IsGeometricallyConnected := ArithmeticGroups.Lattices.ConnectedBaseChange.Construction.geometrically_connected_baseChange G hsimple.1
  let : LieAlgebra.IsSimple Ω (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k Ω))) :=
    infinitesimal_simple_over_algClosed_extension (K := Ω) G hsimple hsemi
  have he : ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange H (algebraMap K Ω) = ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k Ω) := by
    dsimp only [H]
    rw [ArithmeticGroups.Lattices.ConnectedBaseChange.Construction.matrixGroupBaseChange_trans]
    rw [← IsScalarTower.algebraMap_eq k K Ω]
  have hi : LieAlgebra.IsSimple Ω (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange H (algebraMap K Ω))) := by
    rw [he]
    infer_instance
  let : LieAlgebra.IsSimple Ω (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange H (algebraMap K Ω))) := hi
  let : LieAlgebra.IsSimple Ω (Ω ⊗[K] ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H) :=
    SimpleLie.simple_of_LieEquiv (ArithmeticGroups.Lattices.Infinitesimal.ScalarEquiv.Construction.infinitesimalScalarLieEquiv (K := Ω) H hH).symm
  exact SimpleLie.simple_lie_of_baseChange (K := Ω)

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalAlgebraicLieSimplicity
