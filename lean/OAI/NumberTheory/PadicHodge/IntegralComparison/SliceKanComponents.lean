import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatModuleKanExtension

/-! # Slice Kan Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SliceKanComponents

noncomputable section

/-!
# IntegralComparison: pointwise slice extension is indexed by discrete components

The category computing left Kan extension from a slice has one terminal
object for every arrow into the slicing object. Its colimits therefore
reduce to coproducts. This gives exact module extension without any
assumption that the slice-forgetful functor preserves products.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C] (U : C) (X : Cᵒᵖ)

abbrev Index := CostructuredArrow (Over.forget U).op X

def arrow (Y : Index U X) : X.unop ⟶ U := Y.hom.unop ≫ Y.left.unop.hom

theorem arrow_map {Y Z : Index U X} (a : Y ⟶ Z) : arrow U X Y = arrow U X Z := by
  have h := congrArg Quiver.Hom.unop (CostructuredArrow.w a)
  change Z.hom.unop ≫ a.left.unop.left = Y.hom.unop at h
  exact (congrArg (fun t => t ≫ Y.left.unop.hom) h.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (fun t => Z.hom.unop ≫ t) (Over.w a.left.unop)))

def projection : Index U X ⥤ Discrete (X.unop ⟶ U) where
  obj Y := ⟨arrow U X Y⟩
  map a := Discrete.eqToHom (arrow_map U X a)

def inclusion : Discrete (X.unop ⟶ U) ⥤ Index U X :=
  Discrete.functor (fun β => CostructuredArrow.mk (Y := op (Over.mk β)) (𝟙 X))

def unitHom (Y : Index U X) : Y ⟶ (inclusion U X).obj ((projection U X).obj Y) :=
  CostructuredArrow.homMk (Over.homMk Y.hom.unop rfl).op (by
    change Y.hom ≫ 𝟙 X = Y.hom
    exact Category.comp_id _)

theorem hom_unique {Y : Index U X} {β : Discrete (X.unop ⟶ U)}
    (a b : Y ⟶ (inclusion U X).obj β) : a = b := by
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply (Over.forget U).map_injective
  have ha := congrArg Quiver.Hom.unop (CostructuredArrow.w a)
  have hb := congrArg Quiver.Hom.unop (CostructuredArrow.w b)
  change 𝟙 X.unop ≫ a.left.unop.left = Y.hom.unop at ha
  change 𝟙 X.unop ≫ b.left.unop.left = Y.hom.unop at hb
  exact (Category.id_comp _).symm.trans (ha.trans (hb.symm.trans (Category.id_comp _)))

def unit : 𝟭 (Index U X) ⟶ projection U X ⋙ inclusion U X where
  app := unitHom U X
  naturality _ _ _ := hom_unique U X _ _

def counit : inclusion U X ⋙ projection U X ⟶ 𝟭 (Discrete (X.unop ⟶ U)) where
  app β := Discrete.eqToHom (by change 𝟙 X.unop ≫ β.as = β.as; exact Category.id_comp _)

def adjunction : projection U X ⊣ inclusion U X where
  unit := SliceKanComponents.unit U X
  counit := SliceKanComponents.counit U X
  left_triangle_components _ := Subsingleton.elim _ _
  right_triangle_components _ := hom_unique U X _ _

instance inclusion_final : (inclusion U X).Final := Functor.final_of_adjunction (adjunction U X)

variable (R : Type (max u v)) [Ring R]

theorem exact_colimits : HasExactColimitsOfShape (Index U X) (ModuleCat.{max u v} R) := by
  have : AB4OfSize.{v} (ModuleCat.{max u v} R) := AB4OfSize_shrink _
  exact hasExactColimitsOfShape_of_final (ModuleCat.{max u v} R) (inclusion U X)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SliceKanComponents
