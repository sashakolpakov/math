import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveKernelCharacters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ScalarDescentSymmetry

/-! # Character Translations -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTranslations

noncomputable section

/-!
# CartierDuality: kernel-character lines are invariant under lifted translations
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]

/-- Left translation by an actual section of the group scheme. -/
def pointShift (a : 𝟙_ (Over S) ⟶ A) : A ⟶ A := (toUnit A ≫ a) * 𝟙 A

theorem pointShift_comp (a : 𝟙_ (Over S) ⟶ A) {T : Over S} (x : T ⟶ A) :
    x ≫ pointShift a = (toUnit T ≫ a) * x := by
  simp only [pointShift, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

variable (f : A ⟶ B) [IsMonHom f]

/-- A group morphism commutes with translation by a section and its image. -/
theorem pointShift_square (a : 𝟙_ (Over S) ⟶ A) : pointShift a ≫ f = f ≫ pointShift (a ≫ f) := by
  rw [pointShift_comp]
  simp only [pointShift, MonObj.mul_comp, Category.id_comp, Category.assoc]

/-- Simultaneous left translation preserves the exact kernel difference. -/
theorem kernelDifference_mul_left {T : Over S} (a x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f (a * x) (a * y) (by rw [MonObj.mul_comp, MonObj.mul_comp, h]) =
      KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x y h := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion, KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion]
  group

theorem kernelDifference_pointShift (a : 𝟙_ (Over S) ⟶ A) {T : Over S}
    (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f (x ≫ pointShift a) (y ≫ pointShift a)
      (by
        simp only [Category.assoc, pointShift_square]
        rw [← Category.assoc, h, Category.assoc]) =
      KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x y h :=
  (KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_congr f _ _ _ _ _
    (by rw [MonObj.mul_comp, MonObj.mul_comp, h])
    (pointShift_comp a x) (pointShift_comp a y)).trans
    (kernelDifference_mul_left f (toUnit T ≫ a) x y h)

variable (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

/-- Equality of the native endpoint maps transports the complete scalar expression. -/
theorem differenceScalar_congr {T : Scheme.{u}} (q q' : T ⟶ B.left) (x x' y y' : T ⟶ A.left)
    (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) (hx' : x' ≫ f.left = q') (hy' : y' ≫ f.left = q')
    (hq : q = q') (hxx : x = x') (hyy : y = y') :
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ q x y hx hy = KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ q' x' y' hx' hy' := by
  cases hq
  cases hxx
  cases hyy
  rfl

include hχ in
/-- The difference scalar can be computed in any original over-scheme presentation of a test pair. -/
theorem differenceScalar_over {T : Over S} (q : T.left ⟶ B.left) (x y : T ⟶ A)
    (hx : x.left ≫ f.left = q) (hy : y.left ≫ f.left = q) :
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ q x.left y.left hx hy =
      (χ T (KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x y (Over.OverMorphism.ext (hx.trans hy.symm)))).val := by
  let h : x ≫ f = y ≫ f := Over.OverMorphism.ext (hx.trans hy.symm)
  exact (differenceScalar_congr f χ q (x ≫ f).left x.left x.left y.left y.left hx hy rfl
    (congrArg Over.Hom.left h.symm) hx.symm rfl rfl).trans (KernelScalarRecovery.Construction.KernelCharacters.differenceScalar_native f χ hχ x y h)

include hχ in
/-- A lifted translation preserves the actual scalar cocycle on all native test schemes. -/
theorem differenceScalar_pointShift (a : 𝟙_ (Over S) ⟶ A) {T : Scheme.{u}}
    (q : T ⟶ B.left) (x y : T ⟶ A.left) (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) :
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ (q ≫ (pointShift (a ≫ f)).left) (x ≫ (pointShift a).left)
      (y ≫ (pointShift a).left)
      (by rw [Category.assoc, ← Over.comp_left, pointShift_square, Over.comp_left, ← Category.assoc, hx])
      (by rw [Category.assoc, ← Over.comp_left, pointShift_square, Over.comp_left, ← Category.assoc, hy]) =
        KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ q x y hx hy := by
  let U := Over.mk (q ≫ B.hom)
  let px : U ⟶ A := KernelCharacterGluing.Construction.KernelCharacters.coverPoint f q x hx
  let py : U ⟶ A := KernelCharacterGluing.Construction.KernelCharacters.coverPoint f q y hy
  have hd : px ≫ f = py ≫ f := (KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f q x hx).trans (KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f q y hy).symm
  have hxt : (px ≫ pointShift a).left ≫ f.left = q ≫ (pointShift (a ≫ f)).left := by
    change (x ≫ (pointShift a).left) ≫ f.left = _
    rw [Category.assoc, ← Over.comp_left, pointShift_square, Over.comp_left, ← Category.assoc, hx]
  have hyt : (py ≫ pointShift a).left ≫ f.left = q ≫ (pointShift (a ≫ f)).left := by
    change (y ≫ (pointShift a).left) ≫ f.left = _
    rw [Category.assoc, ← Over.comp_left, pointShift_square, Over.comp_left, ← Category.assoc, hy]
  have hnew := differenceScalar_over f χ hχ _ (px ≫ pointShift a) (py ≫ pointShift a) hxt hyt
  have hpx : px.left ≫ f.left = q := hx
  have hpy : py.left ≫ f.left = q := hy
  have hold := differenceScalar_over f χ hχ (T := U) q px py hpx hpy
  exact hnew.trans ((congrArg (fun z => (χ U z).val) (kernelDifference_pointShift f a px py hd)).trans hold.symm)

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

/-- The actual character line is invariant under every translation that lifts to the cover. -/
theorem characterDescendedLine_pointShift (a : 𝟙_ (Over S) ⟶ A) :
    Nonempty ((Scheme.Modules.pullback (pointShift (a ≫ f)).left).obj
      (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).sheaf ≅ (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).sheaf) :=
  ScalarDescentSymmetry.Construction.LineDescent.scalarDescendedLine_symmetry f.left (pointShift (a ≫ f)).left (pointShift a).left
    (congrArg Over.Hom.left (pointShift_square f a)) (KernelCharacterGluing.Construction.KernelCharacters.characterScalarCocycle f χ hχ)
    (fun q x y hx hy => differenceScalar_pointShift f χ hχ a q x y hx hy)

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTranslations
