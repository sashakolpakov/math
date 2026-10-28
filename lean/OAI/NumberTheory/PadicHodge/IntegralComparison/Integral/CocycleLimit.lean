import OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Compatibility
import OAI.NumberTheory.PadicHodge.IntegralComparison.TateCompatibleCharacters

/-! # Cocycle Limit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CocycleLimit

noncomputable section

/-! Compatible finite H¹ classes give an integral cocycle on the genuine
simultaneous multiplication cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacterNaturality

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)
  (x : ∀ n, (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1)
  (hx : ∀ n, Sheaf.H.map (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left) 1
    (x (n + 1)) = x n)

local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationInfiniteCover.cover ℓ A hℓ
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap.overlap ℓ A hℓ
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap.first ℓ A hℓ
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap.second ℓ A hℓ

def finiteCocycle (n : ℕ) : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.obj (op D) :=
  (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map (InfiniteMultiplicationOverlap.overlapMap ℓ A hℓ n).op
    (MultiplicationCoverCharacter.character ℓ n A hℓ (x n))

include hx in
theorem finiteCocycle_step (n : ℕ) :
    (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left).hom.app (op D)
      (finiteCocycle ℓ A hℓ x (n + 1)) = finiteCocycle ℓ A hℓ x n := by
  unfold finiteCocycle
  rw [NatTrans.naturality_apply, FiniteCoefficient.Compatibility.overlap_transition,
    hx, CoverCharacterNaturality.restriction_comp, InfiniteMultiplicationOverlap.overlapMap_step]

include hx in
theorem finiteCocycle_coherent (m n : ℕ) (h : m ≤ n) :
    (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ m n h A.left).hom.app (op D)
      (finiteCocycle ℓ A hℓ x n) = finiteCocycle ℓ A hℓ x m := by
  apply ULift.ext
  apply ContinuousMap.ext
  intro z
  refine TateCompatibleCharacters.coherent_of_step ℓ
    (fun n => ULift.down (α := C((D).left, ZMod (ℓ ^ n))) (finiteCocycle ℓ A hℓ x n) z)
    ?_ m n h
  intro i
  exact congrArg (fun s : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ i A.left).obj.obj (op D) =>
    ULift.down (α := C((D).left, ZMod (ℓ ^ i))) s z)
      (finiteCocycle_step ℓ A hℓ x hx i)

def integralCocycle : (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ A.left).obj.obj (op D) :=
  (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.integralCoefficientSections_existsUnique ℓ A.left (op D) (finiteCocycle ℓ A hℓ x)
    (finiteCocycle_coherent ℓ A hℓ x hx)).choose

theorem integralCocycle_reduction (n : ℕ) :
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n A.left).hom.app (op D) (integralCocycle ℓ A hℓ x hx) =
      finiteCocycle ℓ A hℓ x n :=
  (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.integralCoefficientSections_existsUnique ℓ A.left (op D) (finiteCocycle ℓ A hℓ x)
    (finiteCocycle_coherent ℓ A hℓ x hx)).choose_spec.1 n

theorem finiteCocycle_condition (n : ℕ) (T : A.left.ProEt) (p q r : T ⟶ D)
    (hpa : p ≫ a = r ≫ a) (hpb : p ≫ b = q ≫ a) (hqb : q ≫ b = r ≫ b) :
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map p.op (finiteCocycle ℓ A hℓ x n) +
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map q.op (finiteCocycle ℓ A hℓ x n) =
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map r.op (finiteCocycle ℓ A hℓ x n) := by
  unfold finiteCocycle
  rw [CoverCharacterNaturality.restriction_comp, CoverCharacterNaturality.restriction_comp, CoverCharacterNaturality.restriction_comp]
  let : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let : PreconnectedSpace (MultiplicationCoverCharacter.cover ℓ n A hℓ).left :=
    inferInstanceAs (PreconnectedSpace A.left)
  exact Finite.CoverCharacter.character_cocycle ℓ n
    (MultiplicationCoverCharacter.cover ℓ n A hℓ)
    (MultiplicationCoverCharacter.overlap ℓ n A hℓ)
    (MultiplicationCoverCharacter.first ℓ n A hℓ)
    (MultiplicationCoverCharacter.second ℓ n A hℓ)
    (FiniteCoefficient.GroupLaw.multiplication_pow_pullback_zero ℓ n A)
    (x n) T (p ≫ InfiniteMultiplicationOverlap.overlapMap ℓ A hℓ n) (q ≫ InfiniteMultiplicationOverlap.overlapMap ℓ A hℓ n)
    (r ≫ InfiniteMultiplicationOverlap.overlapMap ℓ A hℓ n)
    (by rw [Category.assoc, Category.assoc, InfiniteMultiplicationOverlap.overlapMap_first, ← Category.assoc,
      ← Category.assoc, hpa])
    (by rw [Category.assoc, Category.assoc, InfiniteMultiplicationOverlap.overlapMap_first, InfiniteMultiplicationOverlap.overlapMap_second,
      ← Category.assoc, ← Category.assoc, hpb])
    (by rw [Category.assoc, Category.assoc, InfiniteMultiplicationOverlap.overlapMap_second, ← Category.assoc,
      ← Category.assoc, hqb])

theorem integralCocycle_condition (T : A.left.ProEt) (p q r : T ⟶ D)
    (hpa : p ≫ a = r ≫ a) (hpb : p ≫ b = q ≫ a) (hqb : q ≫ b = r ≫ b) :
    (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ A.left).obj.map p.op (integralCocycle ℓ A hℓ x hx) +
      (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ A.left).obj.map q.op (integralCocycle ℓ A hℓ x hx) =
      (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ A.left).obj.map r.op (integralCocycle ℓ A hℓ x hx) := by
  apply AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.integralCoefficientSections_ext ℓ A.left
  intro n
  rw [map_add, NatTrans.naturality_apply, NatTrans.naturality_apply,
    NatTrans.naturality_apply, integralCocycle_reduction]
  exact finiteCocycle_condition ℓ A hℓ x n T p q r hpa hpb hqb

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CocycleLimit
