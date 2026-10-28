import OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricLieSemisimple
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.ScalarEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.PerfectScalarExtension

/-! # Perfect -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Perfect.Construction

noncomputable section

/-! For the actual connected semisimple groups in Lattices, the infinitesimal
Lie algebra is perfect over the original field and every extension field.
Consequently it has no nonzero abelian Lie-algebra characters. -/

open scoped Classical TensorProduct

attribute [local instance] LieRing.ofAssociativeRing

theorem infinitesimal_derived_eq_top
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    LieAlgebra.derivedSeries k (Action.Construction.infinitesimalStabilizer G) 1 = ⊤ := by
  let : LieAlgebra.IsSemisimple (AlgebraicClosure k)
      (Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k)))) :=
    GeometricLieSemisimple.Construction.geometric_infinitesimal_isSemisimple G hsemi
  have hgeom : LieAlgebra.derivedSeries (AlgebraicClosure k)
      (Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k)))) 1 = ⊤ :=
    SemisimpleLieCharacters.Construction.semisimpleLie_derived_eq_top
  have htensor := PerfectScalarExtension.Construction.perfect_of_LieEquiv (ScalarEquiv.Construction.infinitesimalScalarLieEquiv G hconn).symm hgeom
  exact PerfectScalarExtension.Construction.perfect_baseChange_iff.mp htensor

theorem infinitesimal_baseChange_derived_eq_top
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    LieAlgebra.derivedSeries K
      (Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) 1 = ⊤ := by
  have h := infinitesimal_derived_eq_top G hconn hsemi
  exact PerfectScalarExtension.Construction.perfect_of_LieEquiv (ScalarEquiv.Construction.infinitesimalScalarLieEquiv G hconn) (PerfectScalarExtension.Construction.perfect_baseChange_iff.mpr h)

theorem infinitesimal_no_abelian_characters
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    {A : Type*} [LieRing A] [LieAlgebra k A] [IsLieAbelian A]
    (f : Action.Construction.infinitesimalStabilizer G →ₗ⁅k⁆ A) : f = 0 :=
  PerfectScalarExtension.Construction.perfectLie_hom_to_abelian_eq_zero (infinitesimal_derived_eq_top G hconn hsemi) f

theorem infinitesimal_baseChange_no_abelian_characters
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    {A : Type*} [LieRing A] [LieAlgebra K A] [IsLieAbelian A]
    (f : Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) →ₗ⁅K⁆ A) : f = 0 :=
  PerfectScalarExtension.Construction.perfectLie_hom_to_abelian_eq_zero (infinitesimal_baseChange_derived_eq_top G hconn hsemi) f

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Perfect.Construction
