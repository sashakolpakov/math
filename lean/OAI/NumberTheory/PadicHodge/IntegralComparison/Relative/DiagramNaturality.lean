import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramFormMap

/-! # Diagram Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramNaturality

noncomputable section

/-!
# IntegralComparison: diagram-induced relative form maps commute with crystalline restriction
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramFormMap

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H K Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ρ : K ⟶ Q)
  (θ : H ⟶ K) (hθ : θ ≫ ρ = π)

theorem naturality {U V : C} (α : U ⟶ V) (n : ℕ) (ω : RelativeCrystalline.FormData.Forms K Q ρ V n) :
    RelativeCrystalline.FormData.formsMap H Q π α n (DiagramFormMap.map H K Q π ρ θ hθ V n ω) =
      DiagramFormMap.map H K Q π ρ θ hθ U n (RelativeCrystalline.FormData.formsMap K Q ρ α n ω) := by
  let : Algebra (Q.obj V).ring (K.obj V).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ V
  have he : (RelativeCrystalline.FormData.formsMap H Q π α n).comp (DiagramFormMap.map H K Q π ρ θ hθ V n).hom.toAddMonoidHom =
      (DiagramFormMap.map H K Q π ρ θ hθ U n).hom.toAddMonoidHom.comp (RelativeCrystalline.FormData.formsMap K Q ρ α n) := by
    apply PD.FormsCoefficientMap.addHom_ext (Q.obj V).ring (K.obj V).ring
      (K.obj V).ideal (K.obj V).dividedPowers n
    intro a t
    change RelativeCrystalline.FormData.formsMap H Q π α n (DiagramFormMap.map H K Q π ρ θ hθ V n (RelativeCrystalline.FormData.symbol K Q ρ V n a t)) =
      DiagramFormMap.map H K Q π ρ θ hθ U n (RelativeCrystalline.FormData.formsMap K Q ρ α n (RelativeCrystalline.FormData.symbol K Q ρ V n a t))
    rw [DiagramFormMap.map_symbol, RelativeCrystalline.FormMaps.formsMap_symbol,
      RelativeCrystalline.FormMaps.formsMap_symbol, DiagramFormMap.map_symbol]
    have h (a : (K.obj V).ring) : (H.map α).ringMap ((θ.app V).ringMap a) =
        (θ.app U).ringMap ((K.map α).ringMap a) :=
      congrArg (fun τ : H.obj U ⟶ K.obj V => τ.ringMap a) (θ.naturality α)
    exact congrArg₂ (RelativeCrystalline.FormData.symbol H Q π U n) (h a) (funext (fun i => h (t i)))
  exact DFunLike.congr_fun he ω

def presheafMap (n : ℕ) : RelativeCrystalline.ModuleMaps.formsPresheaf K Q ρ n ⟶
    RelativeCrystalline.ModuleMaps.formsPresheaf H Q π n where
  app U := DiagramFormMap.map H K Q π ρ θ hθ U.unop n
  naturality _ _ α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact (DiagramNaturality.naturality H K Q π ρ θ hθ α.unop n ω).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramNaturality
