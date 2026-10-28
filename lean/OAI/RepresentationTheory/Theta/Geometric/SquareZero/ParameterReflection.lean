import OAI.RepresentationTheory.Theta.Geometric.SquareZero.PicardReflection
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass

/-! # Parameter Reflection -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.ParameterReflection

noncomputable section

/-! The actual zero-normalized parameter Picard family reflects
equality across the injected square-zero parameter algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false in
theorem parameterPicardClass_squareZero_reflects
    {V R S : Type} [AddCommGroup V] [Module ℂ V] [Module ℂᵐᵒᵖ V] [IsCentralScalar ℂ V]
    [CommRing R] [Algebra ℂ R] [Nontrivial R] [CommRing S] [Algebra ℂ S] [Nontrivial S]
    (i : V →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap)
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (a b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V) ⟶ P)
    (h : ParameterizedPicardClass.parameterPicardClass Q (Normalized.SquareZeroDescent.complexSquareZeroParameterMap i hsq ≫ a) =
      ParameterizedPicardClass.parameterPicardClass Q (Normalized.SquareZeroDescent.complexSquareZeroParameterMap i hsq ≫ b)) :
    ParameterizedPicardClass.parameterPicardClass Q a = ParameterizedPicardClass.parameterPicardClass Q b := by
  let T := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V)
  let u := Normalized.SquareZeroDescent.complexSquareZeroParameterMap i hsq
  let L := Q.pullback (a ⊗ₘ 𝟙 A.scheme).left
  let N := Q.pullback (b ⊗ₘ 𝟙 A.scheme).left
  have hzL : AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.IsNormalized A T L :=
    (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.normalized_iff_class A T L).mpr
      (ParameterizedPicardClass.parameterLineClass_normalized Q eQ a)
  have hzN : AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.IsNormalized A T N :=
    (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.normalized_iff_class A T N).mpr
      (ParameterizedPicardClass.parameterLineClass_normalized Q eQ b)
  obtain ⟨eL⟩ := hzL
  obtain ⟨eN⟩ := hzN
  have hp : (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R))
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (u ▷ A.scheme).left)) =
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R))
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (N.pullback (u ▷ A.scheme).left)) := by
    have hL : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (u ▷ A.scheme).left) = ParameterizedPicardClass.parameterLineClass Q (u ≫ a) :=
      ParameterizedPicardClass.parameterLineClass_naturality Q a u
    have hN : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (N.pullback (u ▷ A.scheme).left) = ParameterizedPicardClass.parameterLineClass Q (u ≫ b) :=
      ParameterizedPicardClass.parameterLineClass_naturality Q b u
    rw [hL, hN]
    exact h
  have H := PicardReflection.squareZero_normalized_picard_eq_reflects i hi hsq q he A L N eL eN hp
  exact congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)) H

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.ParameterReflection
