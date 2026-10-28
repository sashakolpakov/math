import OAI.RepresentationTheory.Theta.Geometric.SquareZero.FamilyIsoDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductOpenCover
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Square Zero Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.SquareZeroDescent

noncomputable section

/-! An arbitrary comparison over the ambient algebra descends on the
abelian family after its actual zero-section normalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {V R S : Type} [AddCommGroup V] [Module ℂ V] [Module ℂᵐᵒᵖ V] [IsCentralScalar ℂ V]
    [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]

def complexSquareZeroParameterMap (i : V →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V) :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (TrivSqZeroExt ℂ V) R (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq)

theorem complexSquareZeroParameterMap_left (i : V →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0) :
    (complexSquareZeroParameterMap i hsq).left =
      Spec.map (CommRingCat.ofHom (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq).toRingHom) :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv_left ℂ (TrivSqZeroExt ℂ V) R (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq)

set_option backward.isDefEq.respectTransparency false in
theorem normalized_squareZero_iso_descends [Nontrivial R] [Nontrivial S]
    (i : V →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap)
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L N : (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V) ⊗ A.scheme).left.Modules)
    (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
    (eL : (Scheme.Modules.pullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V))).left).obj L ≅
        ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V)).left)
    (eN : (Scheme.Modules.pullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V))).left).obj N ≅
        ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V)).left)
    (e : (Scheme.Modules.pullback (complexSquareZeroParameterMap i hsq ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (complexSquareZeroParameterMap i hsq ▷ A.scheme).left).obj N) :
    ∃! d : L ≅ N,
      (Scheme.Modules.pullback (complexSquareZeroParameterMap i hsq ▷ A.scheme).left).mapIso d =
        AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.normalize A (complexSquareZeroParameterMap i hsq) L N eL eN e := by
  let T := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V)
  let U := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R
  let u := complexSquareZeroParameterMap i hsq
  have : Flat (fst T A.scheme).left := by
    change Flat (pullback.fst T.hom A.scheme.hom)
    infer_instance
  have H : IsPullback (u ▷ A.scheme).left (fst U A.scheme).left (fst T A.scheme).left
      (Spec.map (CommRingCat.ofHom (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq).toRingHom)) := by
    have hu : u.left = Spec.map (CommRingCat.ofHom (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq).toRingHom) :=
      complexSquareZeroParameterMap_left i hsq
    rw [← hu]
    exact AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductOpenCover.PicardProductOpenCover.productMap_isPullback A.scheme u
  exact SquareZero.FamilyIsoDescent.squareZero_flat_family_iso_descent i hi hsq q he (fst T A.scheme).left
    (u ▷ A.scheme).left (fst U A.scheme).left H hL hN
    (AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.normalize A u L N eL eN e)
    (AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardDescent.NormalizedPicard.normalize_compatible A u L N eL eN e hL)

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.SquareZeroDescent
