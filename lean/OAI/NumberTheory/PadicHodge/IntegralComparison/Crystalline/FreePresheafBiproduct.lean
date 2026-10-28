import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FreePresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-! # Free Presheaf Biproduct -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct

noncomputable section

/-!
# IntegralComparison: finite free ambient-ring presheaves are native biproducts
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FreeModule

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (H : C ⥤ BigCrystallineSite.Object p B J δ f) (ι : Type) [Fintype ι]

abbrev ambientPresheaf : Cᵒᵖ ⥤ ModuleCat.{u} B := H.op ⋙ BigCrystallineCohomology.modulePresheaf f

def projection (i : ι) : RelativeCrystalline.FreePresheaf.presheaf H ι ⟶ ambientPresheaf H where
  app U := ModuleCat.ofHom (X := RelativeCrystalline.FreeModule.freeModule H ι U.unop) (Y := (ambientPresheaf H).obj U)
    { toFun := fun x => x i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def fan : Fan (fun _ : ι => ambientPresheaf H) :=
  Fan.mk (RelativeCrystalline.FreePresheaf.presheaf H ι) (projection H ι)

def lift (s : Fan (fun _ : ι => ambientPresheaf H)) : s.pt ⟶ RelativeCrystalline.FreePresheaf.presheaf H ι where
  app U := ModuleCat.ofHom (X := s.pt.obj U) (Y := RelativeCrystalline.FreeModule.freeModule H ι U.unop)
    { toFun := fun x i => ((s.π.app ⟨i⟩).app U) x
      map_add' := fun x y => funext (fun i => ((s.π.app ⟨i⟩).app U).hom.map_add x y)
      map_smul' := fun b x => funext (fun i => ((s.π.app ⟨i⟩).app U).hom.map_smul b x) }
  naturality U V α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    exact congrArg (fun g : s.pt.obj U ⟶ (ambientPresheaf H).obj V => g x) ((s.π.app ⟨i⟩).naturality α)

def isLimit : IsLimit (fan H ι) where
  lift := FreePresheafBiproduct.lift H ι
  fac s j := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  uniq s m hm := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    exact congrArg (fun g : s.pt ⟶ ambientPresheaf H => (g.app U) x) (hm ⟨i⟩)

instance hasFiniteBiproducts : HasFiniteBiproducts (Cᵒᵖ ⥤ ModuleCat.{u} B) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def iso : RelativeCrystalline.FreePresheaf.presheaf H ι ≅ ⨁ (fun _ : ι => ambientPresheaf H) :=
  (FreePresheafBiproduct.isLimit H ι).conePointUniqueUpToIso (biproduct.isLimit (fun _ : ι => ambientPresheaf H))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct
