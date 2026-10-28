import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityCoordinateSwap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupAssociativity

/-! # Vertical Associativity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalAssociativity.Construction

noncomputable section

/-! The original vertical Poincare product is associative on all
test schemes. The parameter uses three abelian coordinates and the
original dual coordinate, mapped back to the original factor order. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

attribute [local instance] AssociativeParameter.Construction.lineAssociativeParameter_smooth AssociativeParameter.Construction.lineAssociativeParameter_proper AssociativeParameter.Construction.lineAssociativeParameter_connected

theorem poincareVerticalProduct_associative {T : Over (Spec (.of k))}
    (x y z xy yz w : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (hxy : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) x y xy)
    (hyz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) y z yz)
    (hxw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) x yz w)
    (hzw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) xy z w)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U))
    (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) z, U)) :
    (VerticalProduct.Construction.poincareVerticalProduct D x yz w hxw).app U m ((VerticalProduct.Construction.poincareVerticalProduct D y z yz hyz).app U n p) =
      (VerticalProduct.Construction.poincareVerticalProduct D xy z w hzw).app U ((VerticalProduct.Construction.poincareVerticalProduct D x y xy hxy).app U m n) p := by
  let x₀ := AssociativeParameters.Construction.lineAssociativePoint1 A.scheme D.abelian.scheme ≫ (β_ A.scheme D.abelian.scheme).hom
  let y₀ := AssociativeParameters.Construction.lineAssociativePoint2 A.scheme D.abelian.scheme ≫ (β_ A.scheme D.abelian.scheme).hom
  let z₀ := AssociativeParameters.Construction.lineAssociativePoint3 A.scheme D.abelian.scheme ≫ (β_ A.scheme D.abelian.scheme).hom
  let xy₀ := AssociativeParameters.Construction.lineAssociativePoint12 A.scheme D.abelian.scheme ≫ (β_ A.scheme D.abelian.scheme).hom
  let yz₀ := AssociativeParameters.Construction.lineAssociativePoint23 A.scheme D.abelian.scheme ≫ (β_ A.scheme D.abelian.scheme).hom
  let w₀ := AssociativeParameters.Construction.lineAssociativePoint123 A.scheme D.abelian.scheme ≫ (β_ A.scheme D.abelian.scheme).hom
  let xs := x ≫ (β_ D.abelian.scheme A.scheme).hom
  let ys := y ≫ (β_ D.abelian.scheme A.scheme).hom
  let zs := z ≫ (β_ D.abelian.scheme A.scheme).hom
  let r := AssociativeParameterFactors.Construction.lineAssociativeParameterLift xs ys zs
  have hsxy := AssociativityCoordinateSwap.Construction.verticalProductRel_coordinateSwap hxy
  have hsyz := AssociativityCoordinateSwap.Construction.verticalProductRel_coordinateSwap hyz
  have hszw := AssociativityCoordinateSwap.Construction.verticalProductRel_coordinateSwap hzw
  have hx : r ≫ x₀ = x := AssociativityCoordinateSwap.Construction.associativeCoordinateSwap_factor r _ x
    (AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point1 xs ys zs)
  have hy : r ≫ y₀ = y := AssociativityCoordinateSwap.Construction.associativeCoordinateSwap_factor r _ y
    (AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point2 xs ys zs hsxy.2.1)
  have hz : r ≫ z₀ = z := AssociativityCoordinateSwap.Construction.associativeCoordinateSwap_factor r _ z
    (AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point3 xs ys zs (hsxy.2.1.trans hsyz.2.1))
  have hxy' : r ≫ xy₀ = xy := AssociativityCoordinateSwap.Construction.associativeCoordinateSwap_factor r _ xy
    (AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point12 xs ys zs _ hsxy)
  have hyz' : r ≫ yz₀ = yz := AssociativityCoordinateSwap.Construction.associativeCoordinateSwap_factor r _ yz
    (AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point23 xs ys zs _ hsxy.2.1 hsyz)
  have hw : r ≫ w₀ = w := AssociativityCoordinateSwap.Construction.associativeCoordinateSwap_factor r _ w
    (AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point123 xs ys zs _ _ hsxy hszw)
  have h₁₂ := AssociativityCoordinateSwap.Construction.horizontalProductRel_coordinateSwap (AssociativeParameters.Construction.lineAssociativeRelation12 A.scheme D.abelian.scheme)
  have h₂₃ := AssociativityCoordinateSwap.Construction.horizontalProductRel_coordinateSwap (AssociativeParameters.Construction.lineAssociativeRelation23 A.scheme D.abelian.scheme)
  have h₁₂₃ := AssociativityCoordinateSwap.Construction.horizontalProductRel_coordinateSwap (AssociativeParameters.Construction.lineAssociativeRelation1_23 A.scheme D.abelian.scheme)
  have h₁₂₃' := AssociativityCoordinateSwap.Construction.horizontalProductRel_coordinateSwap (AssociativeParameters.Construction.lineAssociativeRelation12_3 A.scheme D.abelian.scheme)
  have hg := GroupAssociativity.Construction.poincareVerticalGroupProduct_associative D x₀ y₀ z₀ xy₀ yz₀ w₀ h₁₂ h₂₃ h₁₂₃ h₁₂₃'
  have hp := FiberAssociativity.Construction.fiberBilinear_associative_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) r
    x₀ y₀ z₀ xy₀ yz₀ w₀ x y z xy yz w hx hy hz hxy' hyz' hw
    (VerticalProduct.Construction.poincareVerticalProduct D y₀ z₀ yz₀ h₂₃) (VerticalProduct.Construction.poincareVerticalProduct D x₀ yz₀ w₀ h₁₂₃)
    (VerticalProduct.Construction.poincareVerticalProduct D x₀ y₀ xy₀ h₁₂) (VerticalProduct.Construction.poincareVerticalProduct D xy₀ z₀ w₀ h₁₂₃') hg U m n p
  rw [VerticalProduct.Construction.poincareVerticalProduct_natural D r x₀ yz₀ w₀ h₁₂₃ x yz w hxw hx hyz' hw,
    VerticalProduct.Construction.poincareVerticalProduct_natural D r y₀ z₀ yz₀ h₂₃ y z yz hyz hy hz hyz',
    VerticalProduct.Construction.poincareVerticalProduct_natural D r xy₀ z₀ w₀ h₁₂₃' xy z w hzw hxy' hz hw,
    VerticalProduct.Construction.poincareVerticalProduct_natural D r x₀ y₀ xy₀ h₁₂ x y xy hxy hx hy hxy'] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalAssociativity.Construction
