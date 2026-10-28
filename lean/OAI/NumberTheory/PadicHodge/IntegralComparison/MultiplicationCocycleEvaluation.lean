import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationOverlapCocycles

/-! # Multiplication Cocycle Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCocycleEvaluation

noncomputable section

/-! The cocycle attached to a torsion character evaluates to that
character along the corresponding deck translation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationOverlapCocycles

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

local notation "N" => ℓ ^ n
local notation "T" => OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A N
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.cover ℓ n A hℓ
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.overlap ℓ n A hℓ
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.first ℓ n A hℓ
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.second ℓ n A hℓ
local notation "m" => ((𝟙 A : A ⟶ A) ^ N)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem pair_difference (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    MultiplicationOverlapCocycles.siteMap A (TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t) ≫
      MultiplicationOverlapCocycles.difference ℓ n A hℓ a b =
        toUnit (MultiplicationOverlapCocycles.siteOver A U) ≫ TorsionPointCharacter.torsionPoint ℓ n A t := by
  let p := TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t
  let j := MultiplicationOverlapCocycles.toA ℓ n A hℓ (𝟙 U)
  have hp₀ : MultiplicationOverlapCocycles.toA ℓ n A hℓ (p ≫ a) = j := by
    apply Over.OverMorphism.ext
    exact TorsionPointCharacter.pair_fst ℓ n A hℓ _ _ t
  have hp₁ : MultiplicationOverlapCocycles.toA ℓ n A hℓ (p ≫ b) = j ≫ TorsionPointCharacter.translation ℓ n A t := by
    apply Over.OverMorphism.ext
    change p.left ≫ (b).left = 𝟙 A.left ≫ _
    rw [Category.id_comp]
    exact TorsionPointCharacter.pair_snd ℓ n A hℓ _ _ t
  have htrans : j ≫ TorsionPointCharacter.translation ℓ n A t =
      j * (toUnit (MultiplicationOverlapCocycles.siteOver A U) ≫ t.val) := by
    rw [TorsionPointCharacter.translation, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, comp_toUnit]
  apply equalizer.hom_ext
  change (MultiplicationOverlapCocycles.siteMap A p ≫ MultiplicationOverlapCocycles.difference ℓ n A hℓ a b) ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N =
    (toUnit (MultiplicationOverlapCocycles.siteOver A U) ≫ TorsionPointCharacter.torsionPoint ℓ n A t) ≫
      AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N
  rw [MultiplicationOverlapCocycles.difference_comp, MultiplicationOverlapCocycles.difference_inclusion, hp₀, hp₁, htrans, mul_div_cancel_left]
  rw [Category.assoc, TorsionPointCharacter.torsionPoint, AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι]

omit [Fact (Nat.Prime ℓ)] [GeometricallyIntegral A.hom] in
theorem cocycle_pair_value (χ : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) →+ ZMod N)
    (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) (z : A.left) :
    ULift.down (α := C(A.left, ZMod N))
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map
        (TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t).op
          (MultiplicationOverlapCocycles.cocycle ℓ n A hℓ χ)) z = χ (Additive.ofMul t) := by
  let p := TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t
  change MultiplicationOverlapCocycles.schemeFunction ℓ n A hℓ χ ((MultiplicationOverlapCocycles.siteMap A p ≫ MultiplicationOverlapCocycles.difference ℓ n A hℓ a b).left z) = _
  rw [pair_difference]
  change MultiplicationOverlapCocycles.schemeFunction ℓ n A hℓ χ
    ((TorsionPointCharacter.torsionPoint ℓ n A t).left ((toUnit (MultiplicationOverlapCocycles.siteOver A U)).left z)) = _
  rw [show (toUnit (MultiplicationOverlapCocycles.siteOver A U)).left z = IsLocalRing.closedPoint k from
    Subsingleton.elim (α := Spec (.of k)) _ _, MultiplicationOverlapCocycles.schemeFunction_point]
  apply congrArg χ
  apply congrArg Additive.ofMul
  apply Subtype.ext
  exact AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι N t.val t.property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCocycleEvaluation
