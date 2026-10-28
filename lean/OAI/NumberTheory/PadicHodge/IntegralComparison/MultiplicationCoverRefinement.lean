import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationOverlapCocycles

/-! # Multiplication Cover Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverRefinement

noncomputable section

/-! Multiplication by ℓ refines the ℓ-power multiplication covers and
induces the genuine transition between their torsion-point groups. -/

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

local notation "μℓ" => ((𝟙 A : A ⟶ A) ^ ℓ)
local notation "m" => ((𝟙 A : A ⟶ A) ^ (ℓ ^ n))
local notation "m'" => ((𝟙 A : A ⟶ A) ^ (ℓ ^ (n + 1)))

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem multiplication_comp : μℓ ≫ m = m' := by
  rw [MonObj.comp_pow, Category.comp_id, ← pow_mul, ← Nat.pow_succ']

def coverMap : MultiplicationCoverCharacter.cover ℓ (n + 1) A hℓ ⟶ MultiplicationCoverCharacter.cover ℓ n A hℓ :=
  MorphismProperty.Over.homMk (μℓ).left (congrArg Over.Hom.left (multiplication_comp ℓ n A))

def overlapMap : MultiplicationCoverCharacter.overlap ℓ (n + 1) A hℓ ⟶ MultiplicationCoverCharacter.overlap ℓ n A hℓ :=
  MorphismProperty.Over.homMk
    (pullback.lift
      (pullback.fst (m').left (m').left ≫ (μℓ).left)
      (pullback.snd (m').left (m').left ≫ (μℓ).left) (by
        rw [Category.assoc, Category.assoc,
          ← Over.comp_left, multiplication_comp]
        exact pullback.condition)) (by
      change _ ≫ (pullback.fst (m).left (m).left ≫ (m).left) = _
      rw [← Category.assoc, pullback.lift_fst, Category.assoc,
        ← Over.comp_left, multiplication_comp]
      rfl)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem overlapMap_first : overlapMap ℓ n A hℓ ≫ MultiplicationCoverCharacter.first ℓ n A hℓ =
    MultiplicationCoverCharacter.first ℓ (n + 1) A hℓ ≫ coverMap ℓ n A hℓ := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem overlapMap_second : overlapMap ℓ n A hℓ ≫ MultiplicationCoverCharacter.second ℓ n A hℓ =
    MultiplicationCoverCharacter.second ℓ (n + 1) A hℓ ≫ coverMap ℓ n A hℓ := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

def pointMap : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ (n + 1)) →*
    AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ n) where
  toFun t := ⟨t.val ^ ℓ, by
    change (t.val ^ ℓ) ^ (ℓ ^ n) = 1
    rw [← pow_mul, ← Nat.pow_succ']
    exact t.property⟩
  map_one' := Subtype.ext (one_pow ℓ)
  map_mul' t s := Subtype.ext (mul_pow t.val s.val ℓ)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem toA_coverMap {V : A.left.ProEt} (f : V ⟶ MultiplicationCoverCharacter.cover ℓ (n + 1) A hℓ) :
    MultiplicationOverlapCocycles.toA ℓ n A hℓ (f ≫ coverMap ℓ n A hℓ) =
      MultiplicationOverlapCocycles.toA ℓ (n + 1) A hℓ f ^ ℓ := by
  rw [← Category.comp_id (MultiplicationOverlapCocycles.toA ℓ (n + 1) A hℓ f),
    ← MonObj.comp_pow]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverRefinement
