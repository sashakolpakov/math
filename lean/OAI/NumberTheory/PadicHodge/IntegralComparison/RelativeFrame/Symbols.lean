import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormMaps
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrderedPD

/-! # Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Symbols

noncomputable section

/-!
# IntegralComparison: coordinate differential symbols from a fixed frame are natural
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)
  (F : BigCrystallineSite.Object p B J δ f) (τ : H ⟶ (Functor.const C).obj F)
  (σ : Type u) (x : σ → F.ring)

def coordinate (U : C) (i : σ) : (H.obj U).ring := (τ.app U).ringMap (x i)

theorem coordinate_natural {U V : C} (α : U ⟶ V) (i : σ) :
    (H.map α).ringMap (coordinate H F τ σ x V i) = coordinate H F τ σ x U i :=
  congrArg (fun g : H.obj U ⟶ F => g.ringMap (x i)) (τ.naturality α)

def form [LinearOrder σ] (U : C) (n : ℕ) (s : Set.powersetCard σ n) : RelativeCrystalline.FormData.Forms H Q π U n :=
  RelativeCrystalline.FormData.symbol H Q π U n 1 (fun j => coordinate H F τ σ x U (Set.powersetCard.ofFinEmbEquiv.symm s j))

theorem form_natural [LinearOrder σ] {U V : C} (α : U ⟶ V) (n : ℕ) (s : Set.powersetCard σ n) :
    RelativeCrystalline.FormData.formsMap H Q π α n (form H Q π F τ σ x V n s) = form H Q π F τ σ x U n s := by
  have hs := RelativeCrystalline.FormMaps.formsMap_symbol H Q π α n 1
    (fun j => coordinate H F τ σ x V (Set.powersetCard.ofFinEmbEquiv.symm s j))
  have h1 : (H.map α).ringMap (1 : (H.obj V).ring) = (1 : (H.obj U).ring) :=
    (H.map α).ringMap.toRingHom.map_one
  have ht := funext (fun j => coordinate_natural H F τ σ x α (Set.powersetCard.ofFinEmbEquiv.symm s j))
  exact hs.trans (congrArg₂ (RelativeCrystalline.FormData.symbol H Q π U n) h1 ht)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Symbols
