import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.BaseChange

/-! # Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Universal global functions pass through actual isomorphisms and
products. These operations preserve arbitrary further base changes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B : Over S}

theorem GlobalFunctions.Construction.HasUniversalGlobalFunctions.of_iso (hB : GlobalFunctions.Construction.HasUniversalGlobalFunctions B) (e : A ≅ B) :
    GlobalFunctions.Construction.HasUniversalGlobalFunctions A := by
  intro T b
  let e' := (Over.pullback b).mapIso e
  have : IsIso ((Over.pullback b).obj B).hom.appTop := hB T b
  have : IsIso e'.hom.left := (Over.forget T).map_isIso e'.hom
  have : IsIso e'.hom.left.appTop := Scheme.Γ.map_isIso e'.hom.left.op
  change IsIso ((Over.pullback b).obj A).hom.appTop
  rw [← e'.hom.w, Scheme.Hom.comp_appTop]
  infer_instance

theorem UniversalFunction.Products.Construction.universalFunction_product_appTop (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A)
    (hB : GlobalFunctions.Construction.HasUniversalGlobalFunctions B) : IsIso (A ⊗ B).hom.appTop := by
  have : IsIso (pullback.fst A.hom B.hom).appTop :=
    hB.isIso_of_isPullback (pullback.snd A.hom B.hom) (pullback.fst A.hom B.hom) A.hom
      (IsPullback.of_hasPullback A.hom B.hom).flip
  have : IsIso A.hom.appTop := hA.self
  change IsIso (pullback.fst A.hom B.hom ≫ A.hom).appTop
  rw [Scheme.Hom.comp_appTop]
  infer_instance

theorem GlobalFunctions.Construction.HasUniversalGlobalFunctions.product (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A)
    (hB : GlobalFunctions.Construction.HasUniversalGlobalFunctions B) : GlobalFunctions.Construction.HasUniversalGlobalFunctions (A ⊗ B) := by
  intro T b
  let F := Over.pullback b
  let e := Functor.Monoidal.μIso F A B
  have : IsIso (F.obj A ⊗ F.obj B).hom.appTop :=
    UniversalFunction.Products.Construction.universalFunction_product_appTop (hA.pullback b) (hB.pullback b)
  have : IsIso e.inv.left := (Over.forget T).map_isIso e.inv
  have : IsIso e.inv.left.appTop := Scheme.Γ.map_isIso e.inv.left.op
  change IsIso (F.obj (A ⊗ B)).hom.appTop
  rw [← e.inv.w, Scheme.Hom.comp_appTop]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
