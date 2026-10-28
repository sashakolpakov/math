import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints

/-! # Parameter Character Values -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterCharacterValues

noncomputable section

/-! Character values retain their original test scheme under parameter base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters

variable {S : Scheme.{u}} {Q T : Over S} (a : T ⟶ Q)

/-- Viewing the test scheme over its parameter and then over the base preserves the actual scheme. -/
def testIso : (Over.map Q.hom).obj (Over.mk a.left) ≅ T :=
  Over.isoMk (Iso.refl T.left) (by
    change (𝟙 T.left) ≫ T.hom = a.left ≫ Q.hom
    rw [Category.id_comp, a.w])

/-- The comparison preserves the specified parameter point. -/
theorem testIso_projection : (testIso a).hom ≫ a = AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q (Over.mk a.left) := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

variable {A : Over S} [GrpObj A]

/-- A point in the original family defines a point of the actual base-changed group. -/
def point (x : T ⟶ A) : Over.mk a.left ⟶ (Over.pullback Q.hom).obj A :=
  AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) (Over.mk a.left) ((testIso a).hom ≫ x)

theorem point_original (x : T ⟶ A) :
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) (Over.mk a.left)).symm (point a x) =
      (testIso a).hom ≫ x :=
  (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) (Over.mk a.left)).symm_apply_apply _

/-- The point map is exactly the original product family map. -/
theorem point_left (x : T ⟶ A) : (point a x).left = (lift a x).left ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q := by
  apply pullback.hom_ext
  · have h := congrArg Over.Hom.left (point_original a x)
    rw [AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.pullbackPoint_original_left] at h
    change (point a x).left ≫ pullback.fst A.hom Q.hom = (𝟙 T.left) ≫ x.left at h
    rw [Category.id_comp] at h
    rw [Category.assoc, AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_fst, ← Over.comp_left, lift_snd]
    exact h
  · rw [Category.assoc, AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_snd, ← Over.comp_left, lift_fst]
    exact (point a x).w

variable {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

/-- Original and base-changed kernel evaluation agree as actual regular units. -/
theorem value_eq (z : Over.mk a.left ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f))
    (b : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme f)
    (hb : AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f (Over.mk a.left) z = (testIso a).hom ≫ b) :
    AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ (Over.mk a.left) z =
      AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T (χ.app (.op (Over.mk a)) b) := by
  let v : Over.mk (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q (Over.mk a.left)) ⟶ Over.mk a :=
    Over.homMk (testIso a).hom (testIso_projection a)
  have hn := χ.naturality_apply v.op b
  have hc := (congrArg (χ.app (.op (Over.mk (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q (Over.mk a.left))))) hb).trans hn
  have hu := AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom_natural (testIso a).hom
    (χ.app (.op (Over.mk a)) b)
  apply Units.ext
  have hu' := congrArg Units.val hu
  change (𝟙 T.left : T.left ⟶ T.left).appTop
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T (χ.app (.op (Over.mk a)) b)).val = _ at hu'
  rw [Scheme.Hom.id_appTop] at hu'
  exact (congrArg (fun v => (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom
    ((Over.map Q.hom).obj (Over.mk a.left)) v).val) hc).trans hu'.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterCharacterValues
