import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor

/-! # Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Augmentation

noncomputable section

/-!
# IntegralComparison: canonical augmentation of relative crystalline form complexes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormMaps
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormComplex

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

def ambientPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Q.obj U.unop).ring
  map α := AddCommGrpCat.ofHom (Q.map α.unop).ringMap.toRingHom.toAddMonoidHom
  map_id U := by rw [unop_id, Q.map_id]; rfl
  map_comp α β := by rw [unop_comp, Q.map_comp]; rfl

def constants (U : C) : (Q.obj U).ring →+ FormData.Forms H Q π U 0 := by
  letI : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv (Q.obj U).ring (H.obj U).ring (H.obj U).ideal
    (H.obj U).dividedPowers).symm.toAddEquiv.toAddMonoidHom.comp
      (π.app U).ringMap.toRingHom.toAddMonoidHom

theorem constants_symbol (U : C) (a : (Q.obj U).ring) :
    constants H Q π U a = FormData.symbol H Q π U 0 ((π.app U).ringMap a) (fun i : Fin 0 => i.elim0) := by
  let : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  apply (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv (Q.obj U).ring (H.obj U).ring (H.obj U).ideal
    (H.obj U).dividedPowers).injective
  erw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv_symbol]

theorem constants_natural {U V : C} (α : U ⟶ V) (a : (Q.obj V).ring) :
    FormData.formsMap H Q π α 0 (constants H Q π V a) = constants H Q π U ((Q.map α).ringMap a) := by
  rw [constants_symbol, FormMaps.formsMap_symbol, constants_symbol]
  have h := DFunLike.congr_fun (FormData.ring_square H Q π α) a
  congr 1
  funext i
  exact i.elim0

theorem constants_differential (U : C) (a : (Q.obj U).ring) :
    FormMaps.differential H Q π U 0 (constants H Q π U a) = 0 := by
  let : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  rw [constants_symbol]
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential (Q.obj U).ring (H.obj U).ring (H.obj U).ideal (H.obj U).dividedPowers 0
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol (Q.obj U).ring (H.obj U).ring (H.obj U).ideal (H.obj U).dividedPowers
      (algebraMap (Q.obj U).ring (H.obj U).ring a) (fun i : Fin 0 => i.elim0)) = 0
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor.PDDeRhamTensor.differential_symbol]
  unfold AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol
  have h := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_base (Q.obj U).ring (H.obj U).ring
    (Fin.cons 0 (fun i : Fin 0 => i.elim0)) 0 a
  rw [Fin.update_cons_zero] at h
  rw [h, map_zero]

def augmentationZero : ambientPresheaf Q ⟶ FormComplex.formsPresheaf H Q π 0 where
  app U := AddCommGrpCat.ofHom (constants H Q π U.unop)
  naturality _ _ α := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun a => (constants_natural H Q π α.unop a).symm)

theorem augmentationZero_differential : augmentationZero H Q π ≫
    FormComplex.differential H Q π 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (constants_differential H Q π U.unop)

def augmentation : (CochainComplex.single₀ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj (ambientPresheaf Q) ⟶ FormComplex.complex H Q π :=
  (CochainComplex.fromSingle₀Equiv (FormComplex.complex H Q π) (ambientPresheaf Q)).symm
    ⟨augmentationZero H Q π, by rw [FormComplex.complex_d]; exact augmentationZero_differential H Q π⟩

theorem augmentation_zero : (augmentation H Q π).f 0 = augmentationZero H Q π :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Augmentation
