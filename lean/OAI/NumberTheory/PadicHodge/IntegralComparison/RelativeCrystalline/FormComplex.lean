import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormMaps
import Mathlib.Algebra.Homology.Functor

/-! # Form Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormComplex

noncomputable section

/-!
# IntegralComparison: natural relative forms assemble into the actual presheaf complex
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormMaps

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

theorem formsMap_id (U : C) (n : ℕ) : FormData.formsMap H Q π (𝟙 U) n = AddMonoidHom.id _ := by
  let : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  apply PD.FormsCoefficientMap.addHom_ext (Q.obj U).ring (H.obj U).ring
    (H.obj U).ideal (H.obj U).dividedPowers
  intro a t
  change FormData.formsMap H Q π (𝟙 U) n (FormData.symbol H Q π U n a t) = FormData.symbol H Q π U n a t
  rw [FormMaps.formsMap_symbol, H.map_id]
  rfl

theorem formsMap_comp {U V W : C} (α : U ⟶ V) (β : V ⟶ W) (n : ℕ) :
    FormData.formsMap H Q π (α ≫ β) n = (FormData.formsMap H Q π α n).comp (FormData.formsMap H Q π β n) := by
  let : Algebra (Q.obj W).ring (H.obj W).ring := FormData.relativeAlgebra H Q π W
  apply PD.FormsCoefficientMap.addHom_ext (Q.obj W).ring (H.obj W).ring
    (H.obj W).ideal (H.obj W).dividedPowers
  intro a t
  change FormData.formsMap H Q π (α ≫ β) n (FormData.symbol H Q π W n a t) =
    FormData.formsMap H Q π α n (FormData.formsMap H Q π β n (FormData.symbol H Q π W n a t))
  rw [FormMaps.formsMap_symbol, FormMaps.formsMap_symbol, FormMaps.formsMap_symbol, H.map_comp]
  rfl

def formsPresheaf (n : ℕ) : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (FormData.Forms H Q π U.unop n)
  map α := AddCommGrpCat.ofHom (FormData.formsMap H Q π α.unop n)
  map_id U := by apply AddCommGrpCat.hom_ext; exact formsMap_id H Q π U.unop n
  map_comp α β := by apply AddCommGrpCat.hom_ext; exact formsMap_comp H Q π β.unop α.unop n

def differential (n : ℕ) : formsPresheaf H Q π n ⟶ formsPresheaf H Q π (n + 1) where
  app U := AddCommGrpCat.ofHom (FormMaps.differential H Q π U.unop n)
  naturality _ _ α := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun ω => (FormMaps.formsMap_differential H Q π α.unop n ω).symm)

theorem differential_square (n : ℕ) : differential H Q π n ≫ differential H Q π (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (FormMaps.differential_square H Q π U.unop n)

def complex : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (formsPresheaf H Q π) (differential H Q π) (differential_square H Q π)

theorem complex_d (n : ℕ) : (complex H Q π).d n (n + 1) = differential H Q π n :=
  CochainComplex.of_d _ _ n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormComplex
