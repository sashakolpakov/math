import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

/-! # Form Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormScalars

noncomputable section

/-!
# IntegralComparison: ambient semilinearity of the original frame form map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)
  (F : BigCrystallineSite.Object p B J δ f) (τ : H ⟶ (Functor.const C).obj F)

theorem map_smul (U : C) (n : ℕ) (a : F.ring) (ω : FormMap.frameModule F n) :
    letI : Algebra B F.ring := F.base.toAlgebra
    FormMap.map H Q π F τ U n
      (@SMul.smul F.ring (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form B F.ring F.ideal F.dividedPowers n) inferInstance a ω) =
        @SMul.smul (H.obj U).ring (RelativeCrystalline.FormData.Forms H Q π U n) inferInstance
          ((τ.app U).ringMap a) (FormMap.map H Q π F τ U n ω) := by
  let : Algebra B F.ring := F.base.toAlgebra
  let : Algebra B (Q.obj U).ring := (Q.obj U).base.toAlgebra
  let : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  let : Algebra B (H.obj U).ring := FormMap.compositeBase H Q π U
  let : IsScalarTower B (Q.obj U).ring (H.obj U).ring := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact PD.FormsCoefficientMap.formsMap_smul B (Q.obj U).ring F.ring (H.obj U).ring F.ideal F.dividedPowers
    (H.obj U).ideal (H.obj U).dividedPowers (FormMap.frameAlgebraMap H Q π F τ U) (τ.app U).ringMap.isDPMorphism n a ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormScalars
