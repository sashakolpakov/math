import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.ProductPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterScalarSwap

/-! # Parameter Scalar Product -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterScalarProduct.Construction

noncomputable section

/-! The parameterized descent scalar, on actual morphisms of test
schemes, equals the original product-family scalar in the same coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {Q : Over (Spec (.of k))} (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1)

omit [IsAlgClosed k] in
theorem poincareParameterProductPoint_image (U : Over Q.left)
    (q x : U ⟶ (Over.pullback Q.hom).obj A.scheme)
    (hx : x ≫ (Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n) = q) :
    Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U x ≫ TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n =
      Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U q :=
  (Parameter.ProductPoints.Construction.parameterProductPoint_comp Q U ((𝟙 A.scheme) ^ n) x).symm.trans
    (congrArg (Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U) hx)

set_option backward.isDefEq.respectTransparency false in
theorem poincareParameterDescentScalar_product (U : Over Q.left)
    (q x y : U ⟶ (Over.pullback Q.hom).obj A.scheme)
    (hx : x ≫ (Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n) = q)
    (hy : y ≫ (Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n) = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)).left
        (TorsionParameterLine.Construction.poincareTorsionParameterLine D t).sheaf)
      (TorsionParameterLine.Construction.poincareTorsionParameterPullbackFrame D t n ht).symm q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n).left
      (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t).sheaf) (TorsionPullbackFrame.Construction.poincareTorsionFamilyPullbackFrame D t n ht).symm
      (Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U q).left (Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U x).left
      (Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U y).left
      (congrArg Over.Hom.left (poincareParameterProductPoint_image n U q x hx))
      (congrArg Over.Hom.left (poincareParameterProductPoint_image n U q y hy)) := by
  have hs := ParameterScalarSwap.Construction.poincareParameterDescentScalar_swap D t n ht q.left x.left y.left
    (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy)
  exact hs.trans (Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar_congr
    (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n).left
      (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t).sheaf) (TorsionPullbackFrame.Construction.poincareTorsionFamilyPullbackFrame D t n ht).symm
    _ _ _ _ _ _ _ _ _ _ (Parameter.ProductPoints.Construction.parameterProductPoint_left Q A.scheme U q).symm
      (Parameter.ProductPoints.Construction.parameterProductPoint_left Q A.scheme U x).symm (Parameter.ProductPoints.Construction.parameterProductPoint_left Q A.scheme U y).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterScalarProduct.Construction
