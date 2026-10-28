import OAI.NumberTheory.Quaternion.Arithmetic.AdjointClosed
import OAI.NumberTheory.Quaternion.Arithmetic.LieIdealOrbit
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormal

/-! # Connected Adjoint Ideals -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ConnectedAdjointIdeals

noncomputable section

/-! On a connected algebraic group with semisimple Lie algebra, the
adjoint action fixes every Lie ideal: its finite orbit has closed fibers. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormal.Construction Set

attribute [local instance] LieRing.ofAssociativeRing

variable {k : Type} [Field k] {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n)

local instance connectedAdjointRationalTopology : TopologicalSpace G.RationalPoints := ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology G

def matrixIdealSubspace (I : LieIdeal k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)) :
    Submodule k (Matrix (Fin n) (Fin n) k) :=
  I.toSubmodule.map (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule.subtype

theorem mem_matrixIdealSubspace (I : LieIdeal k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G))
    (X : ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) : X.val ∈ matrixIdealSubspace G I ↔ X ∈ I := by
  constructor
  · rintro ⟨Y, hY, he⟩
    exact Subtype.ext he ▸ hY
  · intro hX
    exact ⟨X, hX, rfl⟩

theorem rational_adjoint_ideal_mem_closed
    (I : LieIdeal k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)) (X : ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    IsClosed {g : G.RationalPoints | ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G g X ∈ I} := by
  have he : {g : G.RationalPoints | ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G g X ∈ I} =
      {g : G.RationalPoints | (g.val : Matrix (Fin n) (Fin n) k) * X.val *
        ((g⁻¹).val : Matrix (Fin n) (Fin n) k) ∈ matrixIdealSubspace G I} := by
    ext g
    have hg := ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint_apply G g X
    exact (mem_matrixIdealSubspace G I (ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G g X)).symm.trans
      (Iff.of_eq (congrArg (fun A => A ∈ matrixIdealSubspace G I) hg))
  rw [he]
  exact AdjointClosed.rational_adjoint_subspace_closed G X.val (matrixIdealSubspace G I)

theorem rational_adjoint_ideal_fiber_closed
    (I J : LieIdeal k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)) :
    IsClosed {g : G.RationalPoints | I.map (ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G g).toLieHom = J} := by
  have he : {g : G.RationalPoints | I.map (ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G g).toLieHom = J} =
      {g : G.RationalPoints | Module.finrank k I = Module.finrank k J} ∩
        ⋂ X : I, {g : G.RationalPoints | ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G g X.val ∈ J} := by
    ext g
    simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq, LieIdealOrbit.lieIdeal_image_eq_iff]
    exact ⟨fun h => ⟨h.1, fun X => h.2 X.val X.property⟩,
      fun h => ⟨h.1, fun X hX => h.2 ⟨X, hX⟩⟩⟩
  rw [he]
  apply IsClosed.inter
  · by_cases hd : Module.finrank k I = Module.finrank k J <;> simp [hd]
  · exact isClosed_iInter (fun X => rational_adjoint_ideal_mem_closed G J X.val)

theorem connected_adjoint_ideal_image_eq
    [PreconnectedSpace G.RationalPoints]
    [LieAlgebra.IsSemisimple k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)]
    (I : LieIdeal k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)) (g : G.RationalPoints) :
    I.map (ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G g).toLieHom = I := by
  let : Finite (LieIdeal k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)) :=
    FiniteLieIdeals.finite_lieIdeals_of_semisimple k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)
  have hc := FiniteConnectedAction.finite_closed_fibers_constant
    (fun h : G.RationalPoints => I.map (ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G h).toLieHom)
    (fun J => rational_adjoint_ideal_fiber_closed G I J) 1 g
  have h1 : I.map (ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G 1).toLieHom = I := by
    apply (LieIdealOrbit.lieIdeal_image_eq_iff _ I I).mpr
    refine ⟨rfl, ?_⟩
    intro X hX
    have he : ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G 1 X = X := by
      apply Subtype.ext
      rw [ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint_apply]
      simp only [OneMemClass.coe_one, inv_one, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_mul, Matrix.mul_one]
    rwa [he]
  exact hc.trans h1

theorem connected_adjoint_preserves_ideal
    [PreconnectedSpace G.RationalPoints]
    [LieAlgebra.IsSemisimple k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)]
    (I : LieIdeal k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)) (g : G.RationalPoints)
    {X : ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G} (hX : X ∈ I) : ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G g X ∈ I := by
  rw [← connected_adjoint_ideal_image_eq G I g]
  exact LieIdeal.mem_map hX

end

end OAI.NumberTheory.Quaternion.Arithmetic.ConnectedAdjointIdeals
