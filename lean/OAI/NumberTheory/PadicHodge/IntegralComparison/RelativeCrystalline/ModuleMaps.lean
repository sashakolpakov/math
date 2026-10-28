import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormComplex

/-! # Module Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleMaps

noncomputable section

/-!
# IntegralComparison: relative crystalline forms with the original base scalars
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormMaps

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

theorem formsMap_coefficient_smul {U V : C} (α : U ⟶ V) (n : ℕ)
    (a : (Q.obj V).ring) (ω : FormData.Forms H Q π V n) :
    letI : Algebra (Q.obj V).ring (H.obj V).ring := FormData.relativeAlgebra H Q π V
    letI : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
    FormData.formsMap H Q π α n (a • ω) = (Q.map α).ringMap a • FormData.formsMap H Q π α n ω := by
  let : Algebra (Q.obj V).ring (H.obj V).ring := FormData.relativeAlgebra H Q π V
  let : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  rw [← algebraMap_smul (H.obj V).ring a ω, FormMaps.formsMap_smul]
  have h : (H.map α).ringMap ((π.app V).ringMap a) =
      (π.app U).ringMap ((Q.map α).ringMap a) :=
    DFunLike.congr_fun (FormData.ring_square H Q π α) a
  change (H.map α).ringMap ((π.app V).ringMap a) • FormData.formsMap H Q π α n ω = _
  rw [h]
  exact algebraMap_smul (H.obj U).ring ((Q.map α).ringMap a) _

def formsModule (U : C) (n : ℕ) : ModuleCat.{u} B := by
  letI : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact (ModuleCat.restrictScalars (Q.obj U).base).obj
    (ModuleCat.of (Q.obj U).ring (FormData.Forms H Q π U n))

def map {U V : C} (α : U ⟶ V) (n : ℕ) : formsModule H Q π V n ⟶ formsModule H Q π U n := by
  letI : Algebra (Q.obj V).ring (H.obj V).ring := FormData.relativeAlgebra H Q π V
  letI : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact ModuleCat.ofHom (X := formsModule H Q π V n) (Y := formsModule H Q π U n)
    { toFun := FormData.formsMap H Q π α n
      map_add' := (FormData.formsMap H Q π α n).map_add
      map_smul' := by
        intro b ω
        have h := formsMap_coefficient_smul H Q π α n ((Q.obj V).base b) (ω : FormData.Forms H Q π V n)
        exact h.trans (congrArg (fun a : (Q.obj U).ring => a • FormData.formsMap H Q π α n (ω : FormData.Forms H Q π V n))
          (DFunLike.congr_fun (Q.map α).overBase b)) }

def formsPresheaf (n : ℕ) : Cᵒᵖ ⥤ ModuleCat.{u} B where
  obj U := formsModule H Q π U.unop n
  map α := ModuleMaps.map H Q π α.unop n
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact DFunLike.congr_fun (FormComplex.formsMap_id H Q π U.unop n) ω
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact DFunLike.congr_fun (FormComplex.formsMap_comp H Q π β.unop α.unop n) ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleMaps
