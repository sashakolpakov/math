import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterLines

/-! # Parameter Family -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily

noncomputable section

/-!
# CartierDuality: native family maps for restriction of parametrized character lines
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}}

/-- The family comparison preserves the original group coordinate. -/
theorem parameterFamilyMap_fst (B Q : Over S) :
    ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q ≫ pullback.fst B.hom Q.hom = (snd Q B).left := by
  let U := 𝟙_ (Over Q.left)
  let e := AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B Q.hom U
  have hn : e.hom ≫ (snd ((Over.map Q.hom).obj U) B).left =
      (snd U ((Over.pullback Q.hom).obj B)).left ≫ pullback.fst B.hom Q.hom :=
    AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_snd B Q.hom U
  change ((HomogeneousCharacterLines.Construction.KernelCharacters.baseUnitIso Q).inv ▷ B).left ≫ e.inv ≫
    (snd U ((Over.pullback Q.hom).obj B)).left ≫ pullback.fst B.hom Q.hom = _
  rw [← hn, Iso.inv_hom_id_assoc, ← Over.comp_left, whiskerRight_snd]

/-- The family comparison preserves the parameter coordinate. -/
theorem parameterFamilyMap_snd (B Q : Over S) :
    ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q ≫ pullback.snd B.hom Q.hom = (fst Q B).left := by
  let U := 𝟙_ (Over Q.left)
  let e := AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B Q.hom U
  have hw : (snd U ((Over.pullback Q.hom).obj B)).left ≫ pullback.snd B.hom Q.hom =
      (fst U ((Over.pullback Q.hom).obj B)).left := by
    have h := Over.w (snd U ((Over.pullback Q.hom).obj B))
    exact h
  have hn : e.hom ≫ (fst ((Over.map Q.hom).obj U) B).left =
      (fst U ((Over.pullback Q.hom).obj B)).left := AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_fst B Q.hom U
  change ((HomogeneousCharacterLines.Construction.KernelCharacters.baseUnitIso Q).inv ▷ B).left ≫ e.inv ≫
    (snd U ((Over.pullback Q.hom).obj B)).left ≫ pullback.snd B.hom Q.hom = _
  rw [hw, ← hn, Iso.inv_hom_id_assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left]
  change (fst Q B).left ≫ 𝟙 Q.left = _
  exact Category.comp_id _

/-- The seemingly iterated family comparison is the ordinary interchange of the two fiber-product factors. -/
theorem parameterFamilyMap_eq_symmetry (B Q : Over S) :
    ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q = (pullbackSymmetry Q.hom B.hom).hom := by
  apply pullback.hom_ext
  · exact (parameterFamilyMap_fst B Q).trans (pullbackSymmetry_hom_comp_fst Q.hom B.hom).symm
  · exact (parameterFamilyMap_snd B Q).trans (pullbackSymmetry_hom_comp_snd Q.hom B.hom).symm

/-- Restrict a base-changed group along a morphism of parameter schemes. -/
def parameterPullbackMap (B : Over S) {P Q : Over S} (t : P ⟶ Q) :
    ((Over.pullback P.hom).obj B).left ⟶ ((Over.pullback Q.hom).obj B).left :=
  pullback.map B.hom P.hom B.hom Q.hom (𝟙 B.left) t.left (𝟙 S)
    (by simp) (by simp)

theorem parameterPullbackMap_fst (B : Over S) {P Q : Over S} (t : P ⟶ Q) :
    parameterPullbackMap B t ≫ pullback.fst B.hom Q.hom = pullback.fst B.hom P.hom := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem parameterPullbackMap_snd (B : Over S) {P Q : Over S} (t : P ⟶ Q) :
    parameterPullbackMap B t ≫ pullback.snd B.hom Q.hom = pullback.snd B.hom P.hom ≫ t.left :=
  pullback.lift_snd _ _ _

/-- The original family coordinates commute with restriction to any parameter scheme. -/
theorem parameterFamilyMap_natural (B : Over S) {P Q : Over S} (t : P ⟶ Q) :
    (t ▷ B).left ≫ ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q = ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B P ≫ parameterPullbackMap B t := by
  apply pullback.hom_ext
  · rw [Category.assoc, parameterFamilyMap_fst, Category.assoc, parameterPullbackMap_fst,
      parameterFamilyMap_fst, ← Over.comp_left, whiskerRight_snd]
  · rw [Category.assoc, parameterFamilyMap_snd, Category.assoc, parameterPullbackMap_snd,
      ← Category.assoc, parameterFamilyMap_snd, ← Over.comp_left, whiskerRight_fst, Over.comp_left]

/-- The actual covers commute with the morphism between parameter schemes. -/
theorem parameterPullbackMap_square {A B : Over S} (f : A ⟶ B) {P Q : Over S} (t : P ⟶ Q) :
    parameterPullbackMap A t ≫ ((Over.pullback Q.hom).map f).left =
      ((Over.pullback P.hom).map f).left ≫ parameterPullbackMap B t := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst, parameterPullbackMap_fst]
    rw [← Category.assoc, parameterPullbackMap_fst]
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd, parameterPullbackMap_snd]
    rw [← Category.assoc, pullback.lift_snd]

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily
