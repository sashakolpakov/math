import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FreeModule

/-! # Free Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FreePresheaf

noncomputable section

/-!
# IntegralComparison: a natural finite basis identifies the actual relative form presheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FreeModule

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ι : Type) [Fintype ι]

def map {U V : C} (α : U ⟶ V) : FreeModule.freeModule H ι V ⟶ FreeModule.freeModule H ι U :=
  ModuleCat.ofHom (X := FreeModule.freeModule H ι V) (Y := FreeModule.freeModule H ι U)
    { toFun := fun x i => (H.map α).ringMap (x i)
      map_add' := fun x y => funext (fun i => (H.map α).ringMap.toRingHom.map_add (x i) (y i))
      map_smul' := by
        intro a x
        funext i
        change (H.map α).ringMap ((H.obj V).base a * x i) =
          (H.obj U).base a * (H.map α).ringMap (x i)
        exact ((H.map α).ringMap.toRingHom.map_mul _ _).trans
          (congrArg (fun b : (H.obj U).ring => b * (H.map α).ringMap (x i))
            (DFunLike.congr_fun (H.map α).overBase a)) }

def presheaf : Cᵒᵖ ⥤ ModuleCat.{u} B where
  obj U := FreeModule.freeModule H ι U.unop
  map α := FreePresheaf.map H ι α.unop
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change (H.map (𝟙 U.unop)).ringMap (x i) = x i
    rw [H.map_id]
    rfl
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change (H.map (β.unop ≫ α.unop)).ringMap (x i) =
      (H.map β.unop).ringMap ((H.map α.unop).ringMap (x i))
    rw [H.map_comp]
    rfl

def iso (n : ℕ) (b : ∀ U, Module.Basis ι (H.obj U).ring (FormData.Forms H Q π U n))
    (hb : ∀ {U V} (α : U ⟶ V) i, FormData.formsMap H Q π α n (b V i) = b U i) :
    presheaf H ι ≅ ModuleMaps.formsPresheaf H Q π n :=
  NatIso.ofComponents (fun U => (FreeModule.linearEquiv H Q π ι U.unop n (b U.unop)).toModuleIso) (by
    intro U V α
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (FreeModule.basis_map H Q π ι α.unop n (b V.unop) (b U.unop) (hb α.unop) x).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FreePresheaf
