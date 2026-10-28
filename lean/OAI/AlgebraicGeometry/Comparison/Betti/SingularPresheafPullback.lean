import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Transpose
import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
import Mathlib.Basic.Complex.Basic

/-! # Singular Presheaf Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SingularPresheafPullback

noncomputable section

/-! Pullback of actual singular cochains on all inverse images of open sets. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf

variable {M N : TopCat.{0}} (f : M ⟶ N)

def openPreimageMap (U : Opens N) : TopCat.of ((Opens.map f).obj U) ⟶ TopCat.of U :=
  TopCat.ofHom
    ⟨fun x => ⟨f x, x.property⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk (fun x => x.property)⟩

def openPreimageNat : Opens.map f ⋙ Opens.toTopCat M ⟶ Opens.toTopCat N where
  app := openPreimageMap f
  naturality _ _ _ := by ext x; rfl

def preimagePresheafFunctor : ((Opens M)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ⥤
    ((Opens N)ᵒᵖ ⥤ ModuleCat.{0} ℂ) :=
  (Functor.whiskeringLeft _ _ (ModuleCat.{0} ℂ)).obj (Opens.map f).op

instance preimagePresheafFunctorAdditive : (preimagePresheafFunctor f).Additive where
  map_add := by intros; rfl

def singularCochainPresheafPullback : AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainPresheaf (ModuleCat.of ℂ ℂ) N ⟶
    (Opens.map f).op ⋙ AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainPresheaf (ModuleCat.of ℂ ℂ) M where
  app U := AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (openPreimageMap f U.unop)
  naturality U V i := by
    change AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) ((Opens.toTopCat N).map i.unop) ≫
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (openPreimageMap f V.unop) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (openPreimageMap f U.unop) ≫
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) ((Opens.toTopCat M).map ((Opens.map f).map i.unop))
    let iN : TopCat.of V.unop ⟶ TopCat.of U.unop := (Opens.toTopCat N).map i.unop
    let iM : TopCat.of ((Opens.map f).obj V.unop) ⟶ TopCat.of ((Opens.map f).obj U.unop) :=
      (Opens.toTopCat M).map ((Opens.map f).map i.unop)
    have he : openPreimageMap f V.unop ≫ iN = iM ≫ openPreimageMap f U.unop := by
      ext x
      rfl
    exact (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp (ModuleCat.of ℂ ℂ) (openPreimageMap f V.unop) iN).symm.trans
      ((congrArg (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ)) he).trans
        (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp (ModuleCat.of ℂ ℂ) iM (openPreimageMap f U.unop)))

def singularPresheafPullback : AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) N ⟶
    ((preimagePresheafFunctor f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) M) where
  f n :=
    { app := fun U => ((singularCochainPresheafPullback f).app U).f n
      naturality := fun _U _V i => congrArg (fun k => k.f n)
        ((singularCochainPresheafPullback f).naturality i) }
  comm' i j _ := NatTrans.ext (funext (fun U => ((singularCochainPresheafPullback f).app U).comm i j))

theorem singularPresheafPullback_app (n : ℕ) (U : Opens N) :
    ((singularPresheafPullback f).f n).app (op U) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (openPreimageMap f U)).f n := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.SingularPresheafPullback
