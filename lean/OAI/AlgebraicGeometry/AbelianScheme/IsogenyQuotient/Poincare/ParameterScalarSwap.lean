import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineFrameSquareComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionParameterLine

/-! # Parameter Scalar Swap -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterScalarSwap.Construction

noncomputable section

/-! CartierDuality's parameterized Poincare scalar is the scalar on the original
parameter product, through its actual swap isomorphism and cover square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {Q : Over (Spec (.of k))} (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1)

theorem poincareParameterDescentScalar_swap {T : Scheme}
    (q : T ⟶ ((Over.pullback Q.hom).obj A.scheme).left)
    (x y : T ⟶ ((Over.pullback Q.hom).obj A.scheme).left)
    (hx : x ≫ ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)).left = q)
    (hy : y ≫ ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)).left = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)).left
        (TorsionParameterLine.Construction.poincareTorsionParameterLine D t).sheaf)
      (TorsionParameterLine.Construction.poincareTorsionParameterPullbackFrame D t n ht).symm q x y hx hy =
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n).left
      (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t).sheaf) (TorsionPullbackFrame.Construction.poincareTorsionFamilyPullbackFrame D t n ht).symm
      (q ≫ (pullbackSymmetry Q.hom A.scheme.hom).inv)
      (x ≫ (pullbackSymmetry Q.hom A.scheme.hom).inv)
      (y ≫ (pullbackSymmetry Q.hom A.scheme.hom).inv)
      (by rw [Category.assoc, ← TorsionParameterLine.Construction.poincareParameterMultiplication_square (A := A) Q n, ← Category.assoc, hx])
      (by rw [Category.assoc, ← TorsionParameterLine.Construction.poincareParameterMultiplication_square (A := A) Q n, ← Category.assoc, hy]) := by
  let f := (TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n).left
  let g := ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)).left
  let h := (pullbackSymmetry Q.hom A.scheme.hom).inv
  let hs := TorsionParameterLine.Construction.poincareParameterMultiplication_square (A := A) Q n
  have he := LineFrameSquareComparison.Construction.lineFramePullbackSquare_eq_canonical f g h hs (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t)
    (TorsionPullbackFrame.Construction.poincareTorsionFamilyPullbackFrame D t n ht)
  have hf := congrArg (fun e => Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
    (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent g (TorsionParameterLine.Construction.poincareTorsionParameterLine D t).sheaf) e q x y hx hy) he
  exact hf.trans (Canonical.DescentSquare.Construction.canonicalDescentScalar_square f g h h hs.symm (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t).sheaf
    (TorsionPullbackFrame.Construction.poincareTorsionFamilyPullbackFrame D t n ht).symm q x y hx hy)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterScalarSwap.Construction
