import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange

noncomputable section

/-! Arbitrary base change of constant schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S S' : Scheme.{u}}

/-- The set-valued functor of locally constant labels. -/
def constantSetFunctor (S : Scheme.{u}) (I : Type u) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := LocallyConstant T.unop.left I
  map f := TypeCat.ofHom (LocallyConstant.comap ⟨f.unop.left, f.unop.left.continuous⟩)
  map_id T := by
    ext c x
    rfl
  map_comp f h := by
    ext c x
    rfl

/-- The disjoint union of bases represents the locally constant label functor. -/
def constantSetRepresentable (S : Scheme.{u}) (I : Type u) :
    (constantSetFunctor S I).RepresentableBy (ConstantScheme.Iff.constantScheme S I) where
  homEquiv := ConstantScheme.Iff.constantSchemePointsEquiv S I _
  homEquiv_comp h t := by
    apply LocallyConstant.ext
    intro x
    rfl

/-- Pulling back the constant scheme still represents locally constant labels. -/
def constantSetPullbackRepresentable (f : S' ⟶ S) (I : Type u) :
    (constantSetFunctor S' I).RepresentableBy ((Over.pullback f).obj (ConstantScheme.Iff.constantScheme S I)) where
  homEquiv {T} := ((Over.mapPullbackAdj f).homEquiv T (ConstantScheme.Iff.constantScheme S I)).symm.trans
    (ConstantScheme.Iff.constantSchemePointsEquiv S I ((Over.map f).obj T))
  homEquiv_comp h t := by
    apply LocallyConstant.ext
    intro x
    rfl

/-- A constant scheme commutes with arbitrary changes of the base scheme. -/
def constantSchemeBaseChangeIso (f : S' ⟶ S) (I : Type u) :
    ConstantScheme.Iff.constantScheme S' I ≅ (Over.pullback f).obj (ConstantScheme.Iff.constantScheme S I) :=
  (constantSetRepresentable S' I).uniqueUpToIso (constantSetPullbackRepresentable f I)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange
