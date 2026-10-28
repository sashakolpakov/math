import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Proper Products -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ProperProducts.Construction

noncomputable section

/-! Finite products of proper schemes over a common base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

structure ProperFamilyProduct {S : Scheme.{u}} {ι : Type u} (P : ι → Over S) where
  obj : Over S
  proper : IsProper obj.hom
  projection : ∀ i, obj ⟶ P i
  isLimit : IsLimit (Fan.mk obj projection)

theorem proper_family_has_product
    {S : Scheme.{u}} {ι : Type u} [Finite ι] (P : ι → Over S)
    (hP : ∀ i, IsProper (P i).hom) : Nonempty (ProperFamilyProduct P) := by
  have : MorphismProperty.HasOfPostcompProperty @IsProper @IsProper :=
    ⟨fun f g hg hfg ↦ by have := hg; have := hfg; exact IsProper.of_comp f g⟩
  let : Category (MorphismProperty.Over (@IsProper : MorphismProperty Scheme.{u}) ⊤ S) :=
    MorphismProperty.Comma.instCategory (𝟭 Scheme.{u}) (Functor.fromPUnit.{0} S)
      @IsProper ⊤ ⊤
  let : HasFiniteLimits
      (MorphismProperty.Over (@IsProper : MorphismProperty Scheme.{u}) ⊤ S) :=
    MorphismProperty.Over.hasFiniteLimits @IsProper S
  let : Fintype ι := Fintype.ofFinite ι
  let Q : ι → MorphismProperty.Over (@IsProper : MorphismProperty Scheme.{u}) ⊤ S :=
    fun i ↦ MorphismProperty.Over.mk ⊤ (P i).hom (hP i)
  let F : (MorphismProperty.Over (@IsProper : MorphismProperty Scheme.{u})
      (⊤ : MorphismProperty Scheme.{u}) S) ⥤ Over S :=
    MorphismProperty.Over.forget @IsProper ⊤ S
  have : PreservesFiniteLimits F :=
    MorphismProperty.Over.instPreservesFiniteLimitsTopOverForget @IsProper S
  let A := ∏ᶜ Q
  refine ⟨{
    obj := F.obj A
    proper := A.prop
    projection := fun i ↦ F.map (Pi.π Q i)
    isLimit := isLimitOfHasProductOfPreservesLimit F Q
  }⟩

def ProperFamilyProduct.baseChange
    {S T : Scheme.{u}} {ι : Type u} (g : T ⟶ S) {P : ι → Over S}
    (M : ProperFamilyProduct P) :
    ProperFamilyProduct (fun i ↦ (Over.pullback g).obj (P i)) where
  obj := (Over.pullback g).obj M.obj
  proper := by
    have := M.proper
    exact inferInstanceAs (IsProper (pullback.snd M.obj.hom g))
  projection := fun i ↦ (Over.pullback g).map (M.projection i)
  isLimit := isLimitFanMkObjOfIsLimit (Over.pullback g) P M.projection M.isLimit

def ProperFamilyProduct.lift
    {S : Scheme.{u}} {ι : Type u} {P : ι → Over S} (M : ProperFamilyProduct P)
    (X : Over S) (f : ∀ i, X ⟶ P i) : X ⟶ M.obj :=
  M.isLimit.lift (Fan.mk X f)

@[reassoc (attr := simp)]
theorem ProperFamilyProduct.lift_projection
    {S : Scheme.{u}} {ι : Type u} {P : ι → Over S} (M : ProperFamilyProduct P)
    (X : Over S) (f : ∀ i, X ⟶ P i) (i : ι) :
    M.lift X f ≫ M.projection i = f i :=
  M.isLimit.fac (Fan.mk X f) ⟨i⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ProperProducts.Construction
