import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Augmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

/-! # Module Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex

noncomputable section

/-!
# IntegralComparison: augmented relative form complexes over the original crystalline base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleMaps

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

def differential (n : ℕ) : ModuleMaps.formsPresheaf H Q π n ⟶ ModuleMaps.formsPresheaf H Q π (n + 1) where
  app U := by
    letI : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := FormData.relativeAlgebra H Q π U.unop
    exact (ModuleCat.restrictScalars (Q.obj U.unop).base).map
      (ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential (Q.obj U.unop).ring (H.obj U.unop).ring
        (H.obj U.unop).ideal (H.obj U.unop).dividedPowers n))
  naturality _ _ α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact (FormMaps.formsMap_differential H Q π α.unop n ω).symm

theorem differential_square (n : ℕ) : differential H Q π n ≫ differential H Q π (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact FormMaps.differential_square H Q π U.unop n ω

def complex : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℕ :=
  CochainComplex.of (ModuleMaps.formsPresheaf H Q π) (differential H Q π) (differential_square H Q π)

theorem complex_d (n : ℕ) : (complex H Q π).d n (n + 1) = differential H Q π n :=
  CochainComplex.of_d _ _ n

abbrev ambientPresheaf : Cᵒᵖ ⥤ ModuleCat.{u} B := Q.op ⋙ BigCrystallineCohomology.modulePresheaf f

def constantsLinear (U : C) :
    letI : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
    (Q.obj U).ring →ₗ[(Q.obj U).ring] FormData.Forms H Q π U 0 := by
  letI : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv (Q.obj U).ring (H.obj U).ring (H.obj U).ideal
    (H.obj U).dividedPowers).symm.restrictScalars (Q.obj U).ring).toLinearMap.comp
      (Algebra.linearMap (Q.obj U).ring (H.obj U).ring)

theorem constantsLinear_apply (U : C) (a : (Q.obj U).ring) :
    constantsLinear H Q π U a = Augmentation.constants H Q π U a := rfl

def augmentationZero : ambientPresheaf Q ⟶ ModuleMaps.formsPresheaf H Q π 0 where
  app U := by
    letI : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := FormData.relativeAlgebra H Q π U.unop
    exact ModuleCat.ofHom (X := (ambientPresheaf Q).obj U) (Y := ModuleMaps.formsModule H Q π U.unop 0)
      { toFun := constantsLinear H Q π U.unop
        map_add' := (constantsLinear H Q π U.unop).map_add
        map_smul' := fun b a => (constantsLinear H Q π U.unop).map_smul ((Q.obj U.unop).base b) a }
  naturality _ _ α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (Augmentation.constants_natural H Q π α.unop a).symm

theorem augmentationZero_differential : augmentationZero H Q π ≫ differential H Q π 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Augmentation.constants_differential H Q π U.unop a

def augmentation : (CochainComplex.single₀ _).obj (ambientPresheaf Q) ⟶ complex H Q π :=
  (CochainComplex.fromSingle₀Equiv (complex H Q π) (ambientPresheaf Q)).symm
    ⟨augmentationZero H Q π, by rw [complex_d]; exact augmentationZero_differential H Q π⟩

theorem augmentation_zero : (augmentation H Q π).f 0 = augmentationZero H Q π :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex
