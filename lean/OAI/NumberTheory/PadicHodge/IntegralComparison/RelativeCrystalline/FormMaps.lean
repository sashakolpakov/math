import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

/-! # Form Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormMaps

noncomputable section

/-!
# IntegralComparison: canonical symbols, differentials, and scalar compatibility for relative forms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

def differential (U : C) (n : ℕ) : FormData.Forms H Q π U n →+ FormData.Forms H Q π U (n + 1) := by
  letI : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential (Q.obj U).ring (H.obj U).ring
    (H.obj U).ideal (H.obj U).dividedPowers n).toAddMonoidHom

theorem formsMap_symbol {U V : C} (α : U ⟶ V) (n : ℕ)
    (a : (H.obj V).ring) (t : Fin n → (H.obj V).ring) :
    FormData.formsMap H Q π α n (FormData.symbol H Q π V n a t) =
      FormData.symbol H Q π U n ((H.map α).ringMap a) (fun i => (H.map α).ringMap (t i)) := by
  let : Algebra (Q.obj V).ring (Q.obj U).ring := FormData.coefficientAlgebra Q α
  let : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  let : Algebra (Q.obj V).ring (H.obj V).ring := FormData.relativeAlgebra H Q π V
  let : Algebra (Q.obj V).ring (H.obj U).ring := FormData.compositeAlgebra H Q π α
  let : IsScalarTower (Q.obj V).ring (Q.obj U).ring (H.obj U).ring :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact PD.FormsCoefficientMap.formsMap_symbol (Q.obj V).ring (Q.obj U).ring
    (H.obj V).ring (H.obj U).ring (H.obj V).ideal (H.obj V).dividedPowers
    (H.obj U).ideal (H.obj U).dividedPowers (FormData.mapAlgHom H Q π α) (H.map α).ringMap.isDPMorphism n a t

theorem formsMap_differential {U V : C} (α : U ⟶ V) (n : ℕ) (ω : FormData.Forms H Q π V n) :
    FormData.formsMap H Q π α (n + 1) (differential H Q π V n ω) =
      differential H Q π U n (FormData.formsMap H Q π α n ω) := by
  let : Algebra (Q.obj V).ring (Q.obj U).ring := FormData.coefficientAlgebra Q α
  let : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  let : Algebra (Q.obj V).ring (H.obj V).ring := FormData.relativeAlgebra H Q π V
  let : Algebra (Q.obj V).ring (H.obj U).ring := FormData.compositeAlgebra H Q π α
  let : IsScalarTower (Q.obj V).ring (Q.obj U).ring (H.obj U).ring :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact PD.FormsCoefficientMap.formsMap_differential (Q.obj V).ring (Q.obj U).ring
    (H.obj V).ring (H.obj U).ring (H.obj V).ideal (H.obj V).dividedPowers
    (H.obj U).ideal (H.obj U).dividedPowers (FormData.mapAlgHom H Q π α) (H.map α).ringMap.isDPMorphism n ω

theorem formsMap_smul {U V : C} (α : U ⟶ V) (n : ℕ) (a : (H.obj V).ring) (ω : FormData.Forms H Q π V n) :
    FormData.formsMap H Q π α n (a • ω) = (H.map α).ringMap a • FormData.formsMap H Q π α n ω := by
  let : Algebra (Q.obj V).ring (Q.obj U).ring := FormData.coefficientAlgebra Q α
  let : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  let : Algebra (Q.obj V).ring (H.obj V).ring := FormData.relativeAlgebra H Q π V
  let : Algebra (Q.obj V).ring (H.obj U).ring := FormData.compositeAlgebra H Q π α
  let : IsScalarTower (Q.obj V).ring (Q.obj U).ring (H.obj U).ring :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact PD.FormsCoefficientMap.formsMap_smul (Q.obj V).ring (Q.obj U).ring
    (H.obj V).ring (H.obj U).ring (H.obj V).ideal (H.obj V).dividedPowers
    (H.obj U).ideal (H.obj U).dividedPowers (FormData.mapAlgHom H Q π α) (H.map α).ringMap.isDPMorphism n a ω

theorem differential_square (U : C) (n : ℕ) (ω : FormData.Forms H Q π U n) :
    differential H Q π U (n + 1) (differential H Q π U n ω) = 0 := by
  let : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_square (Q.obj U).ring (H.obj U).ring
    (H.obj U).ideal (H.obj U).dividedPowers n ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormMaps
