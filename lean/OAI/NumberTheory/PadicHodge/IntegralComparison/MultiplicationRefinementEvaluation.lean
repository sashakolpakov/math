import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCocycleEvaluation

/-! # Multiplication Refinement Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationRefinementEvaluation

noncomputable section

/-! Refining the multiplication cover multiplies its deck torsion point
by ℓ. This is the geometric transition in the finite H¹ pairing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationOverlapCocycles
open OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverRefinement

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

local notation "U'" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.cover ℓ (n + 1) A hℓ
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.first ℓ n A hℓ
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.second ℓ n A hℓ
local notation "a'" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.first ℓ (n + 1) A hℓ
local notation "b'" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.second ℓ (n + 1) A hℓ
local notation "m'" => ((𝟙 A : A ⟶ A) ^ (ℓ ^ (n + 1)))

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem pair_difference (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ (n + 1))) :
    MultiplicationOverlapCocycles.siteMap A ((TorsionPointCharacter.pair ℓ (n + 1) A hℓ (𝟙 A)
      (Category.id_comp m') t) ≫ MultiplicationCoverRefinement.overlapMap ℓ n A hℓ) ≫ MultiplicationOverlapCocycles.difference ℓ n A hℓ a b =
        toUnit (MultiplicationOverlapCocycles.siteOver A U') ≫ TorsionPointCharacter.torsionPoint ℓ n A (MultiplicationCoverRefinement.pointMap ℓ n A t) := by
  let p := TorsionPointCharacter.pair ℓ (n + 1) A hℓ (𝟙 A) (Category.id_comp m') t
  have hpa : (p ≫ MultiplicationCoverRefinement.overlapMap ℓ n A hℓ) ≫ a = (p ≫ a') ≫ MultiplicationCoverRefinement.coverMap ℓ n A hℓ := by
    rw [Category.assoc, MultiplicationCoverRefinement.overlapMap_first, Category.assoc]
  have hpb : (p ≫ MultiplicationCoverRefinement.overlapMap ℓ n A hℓ) ≫ b = (p ≫ b') ≫ MultiplicationCoverRefinement.coverMap ℓ n A hℓ := by
    rw [Category.assoc, MultiplicationCoverRefinement.overlapMap_second, Category.assoc]
  have hp : MultiplicationOverlapCocycles.toA ℓ (n + 1) A hℓ (p ≫ b') / MultiplicationOverlapCocycles.toA ℓ (n + 1) A hℓ (p ≫ a') =
      toUnit (MultiplicationOverlapCocycles.siteOver A U') ≫ t.val := by
    have he := congrArg (fun f : MultiplicationOverlapCocycles.siteOver A U' ⟶ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A (ℓ ^ (n + 1)) =>
      f ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A (ℓ ^ (n + 1)))
        (MultiplicationCocycleEvaluation.pair_difference ℓ (n + 1) A hℓ t)
    rw [MultiplicationOverlapCocycles.difference_comp, MultiplicationOverlapCocycles.difference_inclusion, Category.assoc,
      TorsionPointCharacter.torsionPoint, AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι] at he
    exact he
  apply equalizer.hom_ext
  change (MultiplicationOverlapCocycles.siteMap A (p ≫ MultiplicationCoverRefinement.overlapMap ℓ n A hℓ) ≫ MultiplicationOverlapCocycles.difference ℓ n A hℓ a b) ≫
      AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A (ℓ ^ n) =
    (toUnit (MultiplicationOverlapCocycles.siteOver A U') ≫ TorsionPointCharacter.torsionPoint ℓ n A (MultiplicationCoverRefinement.pointMap ℓ n A t)) ≫
      AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A (ℓ ^ n)
  rw [MultiplicationOverlapCocycles.difference_comp, MultiplicationOverlapCocycles.difference_inclusion, hpa, hpb, MultiplicationCoverRefinement.toA_coverMap, MultiplicationCoverRefinement.toA_coverMap,
    ← div_pow, hp, ← MonObj.comp_pow, Category.assoc,
    TorsionPointCharacter.torsionPoint, AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι]
  rfl

omit [Fact (Nat.Prime ℓ)] [GeometricallyIntegral A.hom] in
theorem cocycle_pair_value (χ : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ n)) →+ ZMod (ℓ ^ n))
    (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ (n + 1))) (z : A.left) :
    ULift.down (α := C(A.left, ZMod (ℓ ^ n)))
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map
        ((TorsionPointCharacter.pair ℓ (n + 1) A hℓ (𝟙 A) (Category.id_comp m') t) ≫
          MultiplicationCoverRefinement.overlapMap ℓ n A hℓ).op (MultiplicationOverlapCocycles.cocycle ℓ n A hℓ χ)) z =
            χ (Additive.ofMul (MultiplicationCoverRefinement.pointMap ℓ n A t)) := by
  let p := TorsionPointCharacter.pair ℓ (n + 1) A hℓ (𝟙 A) (Category.id_comp m') t
  change MultiplicationOverlapCocycles.schemeFunction ℓ n A hℓ χ
    ((MultiplicationOverlapCocycles.siteMap A (p ≫ MultiplicationCoverRefinement.overlapMap ℓ n A hℓ) ≫ MultiplicationOverlapCocycles.difference ℓ n A hℓ a b).left z) = _
  rw [pair_difference]
  change MultiplicationOverlapCocycles.schemeFunction ℓ n A hℓ χ
    ((TorsionPointCharacter.torsionPoint ℓ n A (MultiplicationCoverRefinement.pointMap ℓ n A t)).left
      ((toUnit (MultiplicationOverlapCocycles.siteOver A U')).left z)) = _
  rw [show (toUnit (MultiplicationOverlapCocycles.siteOver A U')).left z = IsLocalRing.closedPoint k from
    Subsingleton.elim (α := Spec (.of k)) _ _, MultiplicationOverlapCocycles.schemeFunction_point]
  apply congrArg χ
  apply congrArg Additive.ofMul
  apply Subtype.ext
  exact AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationRefinementEvaluation
