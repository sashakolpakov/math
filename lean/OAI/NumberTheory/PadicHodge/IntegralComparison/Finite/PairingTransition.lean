import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Compatibility
import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationRefinementEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TorsionCharacterEquivalence

/-! # Pairing Transition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PairingTransition

noncomputable section

/-! Reduction of actual finite-coefficient H¹ is compatible with
the ℓ-multiplication transition on torsion points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

theorem transition (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ (n + 1) A.left).H 1)
    (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ (n + 1))) :
    TorsionPointCharacter.character ℓ n A hℓ
      (Sheaf.H.map (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left) 1 x)
        (Additive.ofMul (MultiplicationCoverRefinement.pointMap ℓ n A t)) =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))
        (TorsionPointCharacter.character ℓ (n + 1) A hℓ x (Additive.ofMul t)) := by
  let α := AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left
  let y := Sheaf.H.map α 1 x
  let p := TorsionPointCharacter.pair ℓ (n + 1) A hℓ (𝟙 A)
    (Category.id_comp ((𝟙 A : A ⟶ A) ^ (ℓ ^ (n + 1)))) t
  have he := FiniteCoefficient.Compatibility.overlap_transition ℓ n A hℓ x
  rw [TorsionCharacterEquivalence.character_cocycle_formula ℓ n A hℓ] at he
  have hw := congrArg ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map p.op) he
  rw [← NatTrans.naturality_apply, CoverCharacterNaturality.restriction_comp] at hw
  let : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let z : A.left := Classical.choice inferInstance
  have hv := congrArg (fun s : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.obj
      (op (MultiplicationCoverCharacter.cover ℓ (n + 1) A hℓ)) => ULift.down (α := C(A.left, ZMod (ℓ ^ n))) s z) hw
  change ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))
      (ULift.down (α := C(A.left, ZMod (ℓ ^ (n + 1))))
        ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ (n + 1) A.left).obj.map p.op
          (MultiplicationCoverCharacter.character ℓ (n + 1) A hℓ x)) z) =
    ULift.down (α := C(A.left, ZMod (ℓ ^ n)))
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map
        (p ≫ MultiplicationCoverRefinement.overlapMap ℓ n A hℓ).op
          (MultiplicationOverlapCocycles.cocycle ℓ n A hℓ
            (TorsionPointCharacter.character ℓ n A hℓ y))) z at hv
  rw [TorsionPointCharacter.pair_value,
    MultiplicationRefinementEvaluation.cocycle_pair_value] at hv
  exact hv.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PairingTransition
