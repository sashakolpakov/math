import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.OpenRepresentations

/-! # Base Functor Representation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseFunctorRepresentation

noncomputable section

section

/-! Test schemes whose structural maps lie in an open base have canonical
factorizations, with an explicit equivalence of relative morphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

namespace OpenBaseTest
variable {S : Scheme.{0}} (U : S.Opens) (T : Over S) (hT : ∀ t : T.left, T.hom t ∈ U)

def lift : T.left ⟶ U.toScheme := IsOpenImmersion.lift U.ι T.hom (by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  exact hT t)

theorem lift_ι : OpenBaseTest.lift U T hT ≫ U.ι = T.hom := IsOpenImmersion.lift_fac _ _ _

def over : Over U.toScheme := Over.mk (OpenBaseTest.lift U T hT)

def comparison : T ≅ (Over.map U.ι).obj (over U T hT) :=
  Over.isoMk (Iso.refl T.left) (by
    change 𝟙 T.left ≫ (OpenBaseTest.lift U T hT ≫ U.ι) = T.hom
    rw [Category.id_comp, lift_ι])

def homEquiv (Z : Over U.toScheme) : (T ⟶ (Over.map U.ι).obj Z) ≃ (over U T hT ⟶ Z) where
  toFun f := Over.homMk f.left (by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc]
    exact f.w.trans (lift_ι U T hT).symm)
  invFun f := Over.homMk f.left (by
    change f.left ≫ (Z.hom ≫ U.ι) = T.hom
    rw [← Category.assoc, f.w]
    exact lift_ι U T hT)
  left_inv f := by apply Over.OverMorphism.ext; rfl
  right_inv f := by apply Over.OverMorphism.ext; rfl

theorem homEquiv_comparison (Z : Over U.toScheme) (f : T ⟶ (Over.map U.ι).obj Z) :
    (comparison U T hT).hom ≫ (Over.map U.ι).map (homEquiv U T hT Z f) = f := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

instance reduced [IsReduced T.left] : IsReduced (over U T hT).left :=
  inferInstanceAs (IsReduced T.left)

end OpenBaseTest

end

/-! A representation over an open base gives a literal reduced local
representation of the original functor, on all tests mapping into that open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type) (U : S.Opens)

def reducedOpenRepresentationOfBase (Z : Over U.toScheme) [IsReduced Z.left]
    (u : F.obj (op ((Over.map U.ι).obj Z)))
    (h : ∀ (T : Over U.toScheme) [IsReduced T.left], Function.Bijective
      (fun f : T ⟶ Z => F.map ((Over.map U.ι).map f).op u)) : Reduced.OpenRepresentations.ReducedOpenRepresentation F U where
  space := (Over.map U.ι).obj Z
  reduced := inferInstanceAs (IsReduced Z.left)
  mapsTo z := (Z.hom z).property
  sectionValue := u
  classifies T _ hT := by
    let e := OpenBaseTest.homEquiv U T hT Z
    let q := OpenBaseTest.comparison U T hT
    have hb := (ConcreteCategory.bijective_of_isIso (F.map q.hom.op)).comp
      ((h (OpenBaseTest.over U T hT)).comp e.bijective)
    convert hb using 1
    funext f
    change F.map f.op u = F.map q.hom.op (F.map ((Over.map U.ι).map (e f)).op u)
    rw [← F.map_comp_apply]
    exact congrArg (fun a : T ⟶ (Over.map U.ι).obj Z => F.map a.op u)
      (OpenBaseTest.homEquiv_comparison U T hT Z f).symm

theorem representation_bijective_of_iso {C : Type*} [Category C]
    {F G : Cᵒᵖ ⥤ Type} (e : F ≅ G) (Z : C) (u : F.obj (op Z)) (T : C)
    (h : Function.Bijective (fun f : T ⟶ Z => F.map f.op u)) :
    Function.Bijective (fun f : T ⟶ Z => G.map f.op (e.hom.app (op Z) u)) := by
  have hb := (ConcreteCategory.bijective_of_isIso (e.hom.app (op T))).comp h
  convert hb using 1
  funext f
  exact (ConcreteCategory.congr_hom (e.hom.naturality f.op) u).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseFunctorRepresentation
