import OAI.NumberTheory.Quaternion.Arithmetic.AlmostSimpleLieIdeals
import OAI.NumberTheory.Quaternion.Arithmetic.AlmostSimpleBaseChange
import OAI.NumberTheory.Quaternion.Arithmetic.InfinitesimalNonzero
import OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricLieSemisimple

/-! # Geometric Lie Simplicity -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.GeometricLieSimplicity

noncomputable section

/-! Geometric almost simplicity of the actual semisimple matrix group
implies simplicity of its geometric infinitesimal Lie algebra. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricLieSemisimple.Construction

attribute [local instance] LieRing.ofAssociativeRing

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

theorem geometric_infinitesimal_isSimple
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple) :
    LieAlgebra.IsSimple (AlgebraicClosure k)
      (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k)))) := by
  let H := ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))
  let : TopologicalSpace H.RationalPoints := ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology H
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let : ConnectedSpace G.GeometricPoints := hsimple.1
  let e := GeometricPointTopology.geometricBaseChangePointEquiv G
  let eh := GeometricPointTopology.geometricBaseChangePointHomeomorph G
  let : ConnectedSpace H.RationalPoints := eh.connectedSpace_iff.mpr inferInstance
  let : LieAlgebra.IsSemisimple (AlgebraicClosure k) (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H) :=
    ArithmeticGroups.Lattices.GeometricLieSemisimple.Construction.geometric_infinitesimal_isSemisimple G hsemi
  have hHconn : H.IsGeometricallyConnected := ArithmeticGroups.Lattices.ConnectedBaseChange.Construction.geometrically_connected_baseChange G hsimple.1
  obtain ⟨a, b, hab⟩ := hsimple.2.1
  have ha : a ≠ 1 := by
    intro he
    apply hab
    rw [he, one_mul, mul_one]
  have he : e.symm a ≠ 1 := by
    intro h
    apply ha
    calc
      a = e (e.symm a) := (e.apply_symm_apply a).symm
      _ = e 1 := congrArg e h
      _ = 1 := e.map_one
  have hnonzero : ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H ≠ ⊥ :=
    InfinitesimalNonzero.infinitesimal_nonzero_of_nontrivial_point H hHconn
      (RingHom.id (AlgebraicClosure k)) (e.symm a) he
  constructor
  · exact AlmostSimpleLieIdeals.almostSimple_infinitesimal_ideal_eq_bot_or_top H
      (AlmostSimpleBaseChange.geometricBaseChange_almostSimple_normals G hsimple)
  · intro habel
    let : IsLieAbelian (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H) := habel
    let : Subsingleton (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H) :=
      LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian
        (AlgebraicClosure k) (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H)
    apply hnonzero
    apply le_antisymm _ bot_le
    intro A hA
    change A = 0
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨A, hA⟩ : ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H) 0)

end

end OAI.NumberTheory.Quaternion.Arithmetic.GeometricLieSimplicity
