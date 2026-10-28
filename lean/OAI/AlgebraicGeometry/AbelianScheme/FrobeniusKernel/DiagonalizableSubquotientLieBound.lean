import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteSubquotientCharacterRank
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank

/-! # Diagonalizable Subquotient Lie Bound -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DiagonalizableSubquotientLieBound.Construction

noncomputable section

/-! The character bound is a bound on actual dual-number tangent
points of finite diagonalizable groups, with the original scalar action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

instance finiteAdditiveCharacters (k G : Type) [Field k] [AddCommGroup G] [Finite G] :
    Module.Finite k (G →+ k) := by
  let := Fintype.ofFinite G
  let e : (G →+ k) →ₗ[k] (G → k) := {
    toFun χ := χ
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  exact Module.Finite.of_injective e (fun χ ψ h => AddMonoidHom.ext (congrFun h))

variable {k M : Type} [Field k] [CommGroup M] [Finite M]

theorem diagonalizable_character_tangentRank :
    HodgeConjecture.HeckeCycles.TangentRank.CM.HasRank
      (Grp.mk (RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.groupScheme (k := k) (M := M)))
      (Module.finrank k (Additive M →+ k)) := by
  let e := (Module.finBasis k (Additive M →+ k)).equivFun.symm
  let t := HodgeConjecture.HeckeCycles.DiagonalizableTangentEquiv.CM.tangentEquiv (k := k) (M := M)
  refine ⟨e.toEquiv.trans t, ?_, ?_⟩
  · intro x y
    change RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point (e (x + y)) = _
    rw [map_add, RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point_add]
    rfl
  · intro a x
    change RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point (e (a • x)) = _
    rw [map_smul, ← RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point_scalar]
    rfl

theorem diagonalizable_subquotient_tangentRank_le (m d : ℕ)
    (H : AddSubgroup (Fin d → ZMod m)) (p : H →+ Additive M) (hp : Function.Surjective p) :
    ∃ r ≤ d, HodgeConjecture.HeckeCycles.TangentRank.CM.HasRank
      (Grp.mk (RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.groupScheme (k := k) (M := M))) r :=
  ⟨Module.finrank k (Additive M →+ k), FiniteSubquotientCharacterRank.Construction.finiteCyclicSubquotientCharacter_finrank_le m d H p hp,
    diagonalizable_character_tangentRank⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DiagonalizableSubquotientLieBound.Construction
