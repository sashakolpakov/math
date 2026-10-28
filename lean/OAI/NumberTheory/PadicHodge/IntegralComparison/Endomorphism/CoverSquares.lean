import OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtaleCoverSquares
import OAI.NumberTheory.PadicHodge.IntegralComparison.TorsionPointCharacter

/-! # Cover Squares -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.CoverSquares

noncomputable section

/-! An actual algebraic group endomorphism acts on the multiplication
cover and its overlap, carrying a deck torsion point to its actual image. -/

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
  (hℓ : (ℓ : k) ≠ 0) (e : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)

local notation "N" => ℓ ^ n
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.cover ℓ n A hℓ
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.overlap ℓ n A hℓ
local notation "m" => ((𝟙 A : A ⟶ A) ^ N)
local notation "E" => e.toMul.hom.hom

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem multiplication_comm : E ≫ m = m ≫ E := by
  rw [MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp]

def coverMap : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (E).left).obj U :=
  ProEtaleCoverSquares.map (E).left (E).left
    (congrArg Over.Hom.left (multiplication_comm ℓ n A e))

def overlapSchemeMap : (D).left ⟶ (D).left :=
  pullback.map (m).left (m).left (m).left (m).left (E).left (E).left (E).left
    (congrArg Over.Hom.left (multiplication_comm ℓ n A e).symm)
    (congrArg Over.Hom.left (multiplication_comm ℓ n A e).symm)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc (attr := simp)] theorem overlapSchemeMap_fst :
    overlapSchemeMap ℓ n A hℓ e ≫ (MultiplicationCoverCharacter.first ℓ n A hℓ).left =
      (MultiplicationCoverCharacter.first ℓ n A hℓ).left ≫ (E).left := by
  exact pullback.lift_fst _ _ _

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc (attr := simp)] theorem overlapSchemeMap_snd :
    overlapSchemeMap ℓ n A hℓ e ≫ (MultiplicationCoverCharacter.second ℓ n A hℓ).left =
      (MultiplicationCoverCharacter.second ℓ n A hℓ).left ≫ (E).left := by
  exact pullback.lift_snd _ _ _

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem overlapSchemeMap_comm : overlapSchemeMap ℓ n A hℓ e ≫ (D).hom = (D).hom ≫ (E).left := by
  change overlapSchemeMap ℓ n A hℓ e ≫ ((MultiplicationCoverCharacter.first ℓ n A hℓ).left ≫ (m).left) = _
  rw [← Category.assoc, overlapSchemeMap_fst, Category.assoc]
  have he := congrArg Over.Hom.left (multiplication_comm ℓ n A e)
  change (E).left ≫ (m).left = (m).left ≫ (E).left at he
  rw [he, ← Category.assoc]
  rfl

def overlapMap : D ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (E).left).obj D :=
  ProEtaleCoverSquares.map (E).left (overlapSchemeMap ℓ n A hℓ e)
    (overlapSchemeMap_comm ℓ n A hℓ e)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem overlapMap_first : overlapMap ℓ n A hℓ e ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (E).left).map (MultiplicationCoverCharacter.first ℓ n A hℓ) =
    MultiplicationCoverCharacter.first ℓ n A hℓ ≫ coverMap ℓ n A hℓ e :=
  ProEtaleCoverSquares.naturality (E).left _ _ _ _ _ _ (overlapSchemeMap_fst ℓ n A hℓ e)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem overlapMap_second : overlapMap ℓ n A hℓ e ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (E).left).map (MultiplicationCoverCharacter.second ℓ n A hℓ) =
    MultiplicationCoverCharacter.second ℓ n A hℓ ≫ coverMap ℓ n A hℓ e :=
  ProEtaleCoverSquares.naturality (E).left _ _ _ _ _ _ (overlapSchemeMap_snd ℓ n A hℓ e)

def origin : Spec (.of k) ⟶ A.left := (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A).left

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem one_translation (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) ≫ TorsionPointCharacter.translation ℓ n A t = t.val := by
  rw [TorsionPointCharacter.translation, MonObj.comp_mul, Category.comp_id,
    ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp, _root_.one_mul]

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc (attr := simp)] theorem origin_pair_fst (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    (origin A ≫ (TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t).left) ≫
      (MultiplicationCoverCharacter.first ℓ n A hℓ).left = origin A := by
  rw [Category.assoc, TorsionPointCharacter.pair_fst]
  exact Category.comp_id _

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc (attr := simp)] theorem origin_pair_snd (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    (origin A ≫ (TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t).left) ≫
      (MultiplicationCoverCharacter.second ℓ n A hℓ).left = t.val.left := by
  rw [Category.assoc, TorsionPointCharacter.pair_snd]
  exact congrArg Over.Hom.left (one_translation ℓ n A t)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem origin_pair_map (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    (origin A ≫ (TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t).left) ≫
      overlapSchemeMap ℓ n A hℓ e =
    origin A ≫ (TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m)
      (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.algebraicEndTorsionPointMap A N e t)).left := by
  apply pullback.hom_ext
  · change _ ≫ (MultiplicationCoverCharacter.first ℓ n A hℓ).left = _ ≫ (MultiplicationCoverCharacter.first ℓ n A hℓ).left
    rw [Category.assoc, overlapSchemeMap_fst, ← Category.assoc, origin_pair_fst, origin_pair_fst]
    exact congrArg Over.Hom.left (MonObj.one_comp E)
  · change _ ≫ (MultiplicationCoverCharacter.second ℓ n A hℓ).left = _ ≫ (MultiplicationCoverCharacter.second ℓ n A hℓ).left
    rw [Category.assoc, overlapSchemeMap_snd, ← Category.assoc, origin_pair_snd, origin_pair_snd]
    rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.CoverSquares
