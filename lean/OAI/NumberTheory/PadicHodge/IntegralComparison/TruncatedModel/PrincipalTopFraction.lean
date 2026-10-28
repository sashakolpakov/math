import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafSupportedFraction

/-! # Principal Top Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopFraction

noncomputable section

/-! The literal ordinary fractional top-form class passes through the
actual single-degree inclusion with the original diagonal sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

private theorem class_congr {C : Type u} [Preorder C] [HasFiniteProducts C]
    {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
    {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ) (g : ℕ) (hg : Fintype.card ι=g)
    (q : ℕ) {x y : (K.X q).obj (op (AugmentedOrdered.CechCoordinates.topObject U g hg))}
    (hx : (K.d q (q+1)).app (op (AugmentedOrdered.CechCoordinates.topObject U g hg)) x=0)
    (hy : (K.d q (q+1)).app (op (AugmentedOrdered.CechCoordinates.topObject U g hg)) y=0)
    (h : x=y) : AugmentedOrdered.CechLargeTop.topTotalClass U K g hg q x hx =
      AugmentedOrdered.CechLargeTop.topTotalClass U K g hg q y hy := by
  subst y
  rfl

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens) (g : ℕ) [SmoothOfRelativeDimension g X.hom]
  (a : Fin g → Γ(X.left,U.val))

abbrev family := Supported.Comparison.family p k n X U g a

abbrev numerator (r : WittVector p k) :
    (PrincipalTopSingle.coefficient p k n X U g).obj
      (op (AugmentedOrdered.CechCoordinates.topObject (family p k n X U g a) g (by simp))) :=
  ULift.up.{2,1} (ULift.up.{1,0}
    (Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g
      (PrincipalFraction.topOpen p k n X Y f hp U g a).val
      (PrincipalFraction.fraction p k n X Y f hp U g a r)))

abbrev ordinaryClass (r : WittVector p k) := AugmentedOrdered.CechTopClass.topClass
  (family p k n X U g a) (PrincipalTopSingle.coefficient p k n X U g)
  g (by simp) (numerator p k n X Y f hp U g a r)

abbrev singleClass (r : WittVector p k) :=
  (Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor (family p k n X U g a))
    (PrincipalTopSingle.coefficient p k n X U g) g g).inv
      (ordinaryClass p k n X Y f hp U g a r)

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem coefficient (r : WittVector p k) :
    Augmented.SingleDiagonalClassImage.image (family p k n X U g a)
      (PrincipalTopSingle.coefficient p k n X U g) g (by simp)
      (numerator p k n X Y f hp U g a r)
      (FractionClass.Integral.target p k n X U)
      (PrincipalTopSingle.map p k n X U g) =
    FractionClass.Integral.fraction p k n X Y f hp U g a r :=
  PrincipalTopSingle.component p k n X U g
    (AugmentedOrdered.CechCoordinates.topObject (family p k n X U g a) g (by simp))
    (Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g
      (PrincipalFraction.topOpen p k n X Y f hp U g a).val
      (PrincipalFraction.fraction p k n X Y f hp U g a r))

variable (σ : Type) [LinearOrder σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem image (r : WittVector p k) :
    homologyMap (AugmentedOrdered.CechCoefficientTop.totalMap (family p k n X U g a)
      (PrincipalTopSingle.map p k n X U g)) (g+g)
      (singleClass p k n X Y f hp U g a r) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      FractionClass.Integral.fractionClass p k n X Y f hp U σ g a r := by
  have h := Augmented.SingleDiagonalClassImage.map_apply (family p k n X U g a)
    (PrincipalTopSingle.coefficient p k n X U g) g (by simp)
    (numerator p k n X Y f hp U g a r)
    (FractionClass.Integral.target p k n X U)
    (PrincipalTopSingle.map p k n X U g)
  exact h.trans (congrArg (fun x => ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g • x)
    (class_congr (family p k n X U g a) (FractionClass.Integral.target p k n X U)
      g (by simp) g
      (Augmented.SingleDiagonalClassImage.image_closed (family p k n X U g a)
        (PrincipalTopSingle.coefficient p k n X U g) g (by simp)
        (numerator p k n X Y f hp U g a r)
        (FractionClass.Integral.target p k n X U)
        (PrincipalTopSingle.map p k n X U g))
      (FractionClass.Integral.fraction_closed p k n X Y f hp U σ g a r)
      (coefficient p k n X Y f hp U g a r)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopFraction
