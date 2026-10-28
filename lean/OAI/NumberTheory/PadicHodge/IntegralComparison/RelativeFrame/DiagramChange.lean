import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ChangeNaturality

/-! # Diagram Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.DiagramChange

noncomputable section

/-!
# IntegralComparison: changing a product diagram preserves the fixed-frame section map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}

theorem frameMap_id (F : BigCrystallineSite.Object p B J δ f) :
    ChangeNaturality.frameMap F F (𝟙 F) = 𝟙 (ComplexMap.frameComplex F) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (Crystalline.DeRham.formsPresheaf f n).map_id (op F)

variable (H K Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ρ : K ⟶ Q)
  (θ : H ⟶ K) (hθ : θ ≫ ρ = π) (F : BigCrystallineSite.Object p B J δ f)
  (τ : H ⟶ (Functor.const C).obj F) (υ : K ⟶ (Functor.const C).obj F) (hτ : θ ≫ υ = τ)

include hτ in
theorem complexes : ComplexMap.map K Q ρ F υ ≫
    Relative.DiagramComplexMap.map H K Q π ρ θ hθ = ComplexMap.map H Q π F τ := by
  have hτ' : θ ≫ υ = τ ≫ (Functor.const C).map (𝟙 F) :=
    hτ.trans ((Category.comp_id τ).symm.trans (congrArg (fun a => τ ≫ a) ((Functor.const C).map_id F).symm))
  have h := ChangeNaturality.complexes H K Q π ρ θ hθ F F (𝟙 F) τ υ hτ'
  let M := (Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ Cᵒᵖ ⥤ ModuleCat.{u} B).mapHomologicalComplex (ComplexShape.up ℕ)
  have he : M.map (ChangeNaturality.frameMap F F (𝟙 F)) = 𝟙 _ :=
    (congrArg M.map (frameMap_id F)).trans (M.map_id _)
  exact h.trans ((congrArg (fun a => a ≫ ComplexMap.map H Q π F τ) he).trans
    (Category.id_comp _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.DiagramChange
