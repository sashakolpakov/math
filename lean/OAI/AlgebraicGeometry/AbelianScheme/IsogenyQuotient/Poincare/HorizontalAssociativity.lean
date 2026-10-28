import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameterFactors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupAssociativity

/-! # Horizontal Associativity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.HorizontalAssociativity.Construction

noncomputable section

/-! The original horizontal Poincare product is associative on all
test schemes, by its proper universal associativity configuration. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

attribute [local instance] AssociativeParameter.Construction.lineAssociativeParameter_smooth AssociativeParameter.Construction.lineAssociativeParameter_proper AssociativeParameter.Construction.lineAssociativeParameter_connected

theorem poincareHorizontalProduct_associative {T : Over (Spec (.of k))}
    (x y z xy yz w : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (hxy : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) x y xy)
    (hyz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) y z yz)
    (hxw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) x yz w)
    (hzw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) xy z w)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U))
    (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) z, U)) :
    (HorizontalProduct.Construction.poincareHorizontalProduct D x yz w hxw).app U m ((HorizontalProduct.Construction.poincareHorizontalProduct D y z yz hyz).app U n p) =
      (HorizontalProduct.Construction.poincareHorizontalProduct D xy z w hzw).app U ((HorizontalProduct.Construction.poincareHorizontalProduct D x y xy hxy).app U m n) p := by
  let x₀ := AssociativeParameters.Construction.lineAssociativePoint1 D.abelian.scheme A.scheme
  let y₀ := AssociativeParameters.Construction.lineAssociativePoint2 D.abelian.scheme A.scheme
  let z₀ := AssociativeParameters.Construction.lineAssociativePoint3 D.abelian.scheme A.scheme
  let xy₀ := AssociativeParameters.Construction.lineAssociativePoint12 D.abelian.scheme A.scheme
  let yz₀ := AssociativeParameters.Construction.lineAssociativePoint23 D.abelian.scheme A.scheme
  let w₀ := AssociativeParameters.Construction.lineAssociativePoint123 D.abelian.scheme A.scheme
  let r := AssociativeParameterFactors.Construction.lineAssociativeParameterLift x y z
  have hx : r ≫ x₀ = x := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point1 x y z
  have hy : r ≫ y₀ = y := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point2 x y z hxy.2.1
  have hz : r ≫ z₀ = z := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point3 x y z (hxy.2.1.trans hyz.2.1)
  have hxy' : r ≫ xy₀ = xy := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point12 x y z xy hxy
  have hyz' : r ≫ yz₀ = yz := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point23 x y z yz hxy.2.1 hyz
  have hw : r ≫ w₀ = w := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point123 x y z xy w hxy hzw
  have h₁₂ := AssociativeParameters.Construction.lineAssociativeRelation12 D.abelian.scheme A.scheme
  have h₂₃ := AssociativeParameters.Construction.lineAssociativeRelation23 D.abelian.scheme A.scheme
  have h₁₂₃ := AssociativeParameters.Construction.lineAssociativeRelation1_23 D.abelian.scheme A.scheme
  have h₁₂₃' := AssociativeParameters.Construction.lineAssociativeRelation12_3 D.abelian.scheme A.scheme
  have hg := GroupAssociativity.Construction.poincareHorizontalGroupProduct_associative D x₀ y₀ z₀ xy₀ yz₀ w₀ h₁₂ h₂₃ h₁₂₃ h₁₂₃'
  have hp := FiberAssociativity.Construction.fiberBilinear_associative_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) r
    x₀ y₀ z₀ xy₀ yz₀ w₀ x y z xy yz w hx hy hz hxy' hyz' hw
    (HorizontalProduct.Construction.poincareHorizontalProduct D y₀ z₀ yz₀ h₂₃) (HorizontalProduct.Construction.poincareHorizontalProduct D x₀ yz₀ w₀ h₁₂₃)
    (HorizontalProduct.Construction.poincareHorizontalProduct D x₀ y₀ xy₀ h₁₂) (HorizontalProduct.Construction.poincareHorizontalProduct D xy₀ z₀ w₀ h₁₂₃') hg U m n p
  rw [HorizontalProduct.Construction.poincareHorizontalProduct_natural D r x₀ yz₀ w₀ h₁₂₃ x yz w hxw hx hyz' hw,
    HorizontalProduct.Construction.poincareHorizontalProduct_natural D r y₀ z₀ yz₀ h₂₃ y z yz hyz hy hz hyz',
    HorizontalProduct.Construction.poincareHorizontalProduct_natural D r xy₀ z₀ w₀ h₁₂₃' xy z w hzw hxy' hz hw,
    HorizontalProduct.Construction.poincareHorizontalProduct_natural D r x₀ y₀ xy₀ h₁₂ x y xy hxy hx hy hxy'] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.HorizontalAssociativity.Construction
