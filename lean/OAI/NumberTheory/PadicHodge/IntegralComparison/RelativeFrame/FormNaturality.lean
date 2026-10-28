import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

/-! # Form Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormNaturality

noncomputable section

/-!
# IntegralComparison: frame form maps commute with restriction and the actual differential
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)
  (F : BigCrystallineSite.Object p B J δ f) (τ : H ⟶ (Functor.const C).obj F)

theorem map_differential (U : C) (n : ℕ) (ω : FormMap.frameModule F n) :
    FormMap.map H Q π F τ U (n + 1) (((Crystalline.DeRham.differential f n).app (op F)) ω) =
      RelativeCrystalline.FormMaps.differential H Q π U n (FormMap.map H Q π F τ U n ω) := by
  let : Algebra B F.ring := F.base.toAlgebra
  let : Algebra B (Q.obj U).ring := (Q.obj U).base.toAlgebra
  let : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  let : Algebra B (H.obj U).ring := FormMap.compositeBase H Q π U
  let : IsScalarTower B (Q.obj U).ring (H.obj U).ring := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact PD.FormsCoefficientMap.formsMap_differential B (Q.obj U).ring F.ring (H.obj U).ring F.ideal F.dividedPowers
    (H.obj U).ideal (H.obj U).dividedPowers (FormMap.frameAlgebraMap H Q π F τ U) (τ.app U).ringMap.isDPMorphism n ω

theorem map_natural {U V : C} (α : U ⟶ V) (n : ℕ) (ω : FormMap.frameModule F n) :
    RelativeCrystalline.FormData.formsMap H Q π α n (FormMap.map H Q π F τ V n ω) = FormMap.map H Q π F τ U n ω := by
  let : Algebra B F.ring := F.base.toAlgebra
  have he : (RelativeCrystalline.FormData.formsMap H Q π α n).comp (FormMap.map H Q π F τ V n).hom.toAddMonoidHom =
      (FormMap.map H Q π F τ U n).hom.toAddMonoidHom := by
    apply PD.FormsCoefficientMap.addHom_ext B F.ring F.ideal F.dividedPowers n
    intro a t
    change RelativeCrystalline.FormData.formsMap H Q π α n (FormMap.map H Q π F τ V n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol B F.ring F.ideal F.dividedPowers a t)) =
      FormMap.map H Q π F τ U n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol B F.ring F.ideal F.dividedPowers a t)
    rw [FormMap.map_symbol, RelativeCrystalline.FormMaps.formsMap_symbol, FormMap.map_symbol]
    have h (a : F.ring) : (H.map α).ringMap ((τ.app V).ringMap a) = (τ.app U).ringMap a :=
      congrArg (fun g : H.obj U ⟶ F => g.ringMap a) (τ.naturality α)
    exact congrArg₂ (RelativeCrystalline.FormData.symbol H Q π U n) (h a) (funext (fun i => h (t i)))
  exact DFunLike.congr_fun he ω

def mapPresheaf (n : ℕ) : (Functor.const Cᵒᵖ).obj (FormMap.frameModule F n) ⟶
    RelativeCrystalline.ModuleMaps.formsPresheaf H Q π n where
  app U := FormMap.map H Q π F τ U.unop n
  naturality _ _ α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact (map_natural H Q π F τ α.unop n ω).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormNaturality
