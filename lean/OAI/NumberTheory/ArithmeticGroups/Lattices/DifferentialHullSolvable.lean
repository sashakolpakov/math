import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullInvariant
import OAI.NumberTheory.ArithmeticGroups.Lattices.SolvableLiePreservers

/-! # Differential Hull Solvable -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullSolvable.Construction

noncomputable section

/-! The algebraic hull of a solvable matrix Lie algebra is solvable over
any algebraically closed field of characteristic zero. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

def algebraicMatrixLieRepresentation {k : Type} [Field k] {n : ℕ}
    (S : LieSubalgebra k (Matrix (Fin n) (Fin n) k)) : S →ₗ⁅k⁆ Module.End k (Fin n → k) :=
  lieEquivMatrix'.symm.toLieHom.comp S.incl

local instance algebraicHullLieRingModule {k : Type} [Field k] {n : ℕ}
    (S : LieSubalgebra k (Matrix (Fin n) (Fin n) k)) : LieRingModule S (Fin n → k) :=
  LieRingModule.compLieHom (Fin n → k) (algebraicMatrixLieRepresentation S)

local instance algebraicHullLieModule {k : Type} [Field k] {n : ℕ}
    (S : LieSubalgebra k (Matrix (Fin n) (Fin n) k)) : LieModule k S (Fin n → k) :=
  LieModule.compLieHom (Fin n → k) (algebraicMatrixLieRepresentation S)

theorem differentialHull_solvable
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : LieSubalgebra k (Matrix (Fin n) (Fin n) k))
    [LieAlgebra.IsSolvable S] : Group.IsSolvable (DifferentialHullGroup.Construction.differentialHullSubgroup G S) := by
  let ρ : G.RationalPoints →* ((Fin n → k) ≃ₗ[k] (Fin n → k)) :=
    Matrix.SpecialLinearGroup.toLin'.comp (G.subgroup k (RingHom.id k)).subtype
  have hinj : Function.Injective ρ :=
    Matrix.SpecialLinearGroup.toLin'_injective.comp Subtype.val_injective
  let H := DifferentialHullGroup.Construction.differentialHullSubgroup G S
  apply SolvableLiePreservers.Construction.group_solvable_of_preserves_lie_submodules (L := S) (ρ.comp H.subtype)
    (hinj.comp H.subtype_injective)
  intro W g w hw
  apply DifferentialHullInvariant.Construction.differentialHull_preserves_subspace G S W.toSubmodule _ g hw
  intro A hA x hx
  exact W.lie_mem hx (x := ⟨A, hA⟩)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullSolvable.Construction
