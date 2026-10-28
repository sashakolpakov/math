import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor

/-! # Resolution Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor

noncomputable section

/-! The original bounded relative frame resolutions form a strict contravariant
functor, with a natural structure-sheaf augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n

def diagram : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤ Over Q where
  obj F := Over.mk (IntegralComparison.BoundedFrame.Diagram.projection F)
  map α := Over.homMk (IntegralComparison.BoundedFrame.Change.diagramMap α) (IntegralComparison.BoundedFrame.Change.projection α)
  map_id F := by
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext U
    change (Q).map (prod.map (𝟙 F) (𝟙 U)) = 𝟙 _
    rw [prod.map_id_id, CategoryTheory.Functor.map_id]
  map_comp α β := by
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext U
    change (Q).map (prod.map (α ≫ β) (𝟙 U)) =
      (Q).map (prod.map α (𝟙 U)) ≫ (Q).map (prod.map β (𝟙 U))
    rw [← CategoryTheory.Functor.map_comp]
    apply congrArg (Q).map
    apply prod.hom_ext <;> simp only [Category.assoc, prod.map_fst, prod.map_snd,
      prod.map_fst_assoc, Category.comp_id]

def presheafFunctor : (IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤
    CochainComplex ((IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤ ModuleCat.{u} B) ℕ :=
  (diagram f n).op ⋙ IntegralComparison.Relative.ResolutionFunctor.functor Q

def sheafFunctor : (IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤
    CochainComplex (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n) ℕ :=
  presheafFunctor f n ⋙
    (IntegralComparison.Bounded.RelativeSheafComplex.sheafification f n).mapHomologicalComplex (.up ℕ)

theorem map_eq {F G : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : G ⟶ F) :
    (sheafFunctor f n).map α.op = IntegralComparison.BoundedFrame.Change.sheafMap α := rfl

def augmentation : (Functor.const _).obj
    ((CochainComplex.single₀ _).obj (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf
      (p := p) (J := J) (δ := δ) f n)) ⟶
      sheafFunctor f n where
  app F := IntegralComparison.Bounded.RelativeSheafComplex.augmentation f n F.unop
  naturality _ _ α := (Category.id_comp _).trans (IntegralComparison.BoundedFrame.Change.sheaf_augmentation α.unop).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor
