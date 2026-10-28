import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityCoordinateSwap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupAssociativity

/-! # Vertical Associativity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.VerticalAssociativity.Construction

noncomputable section

/-! The image vertical product is associative on all test schemes,
by pullback from the universal associativity configuration. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable [GrpObj C] [IsMonHom q]

variable [IsCommMonObj C] [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

attribute [local instance] AssociativeParameter.Construction.lineAssociativeParameter_smooth AssociativeParameter.Construction.lineAssociativeParameter_proper AssociativeParameter.Construction.lineAssociativeParameter_connected
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

omit [IsMonHom q] in
theorem picardImageVerticalProduct_associative {T : Over (Spec (.of k))}
    (x y z xy yz w : T ⟶ C ⊗ B)
    (hxy : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) x y xy)
    (hyz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) y z yz)
    (hxw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) x yz w)
    (hzw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) xy z w)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U))
    (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) z, U)) :
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x yz w hxw).app U m ((GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac y z yz hyz).app U n p) =
      (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac xy z w hzw).app U ((GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x y xy hxy).app U m n) p := by
  let x₀ := AssociativeParameters.Construction.lineAssociativePoint1 B C ≫ (β_ B C).hom
  let y₀ := AssociativeParameters.Construction.lineAssociativePoint2 B C ≫ (β_ B C).hom
  let z₀ := AssociativeParameters.Construction.lineAssociativePoint3 B C ≫ (β_ B C).hom
  let xy₀ := AssociativeParameters.Construction.lineAssociativePoint12 B C ≫ (β_ B C).hom
  let yz₀ := AssociativeParameters.Construction.lineAssociativePoint23 B C ≫ (β_ B C).hom
  let w₀ := AssociativeParameters.Construction.lineAssociativePoint123 B C ≫ (β_ B C).hom
  let xs := x ≫ (β_ C B).hom
  let ys := y ≫ (β_ C B).hom
  let zs := z ≫ (β_ C B).hom
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
  have h₁₂ := AssociativityCoordinateSwap.Construction.horizontalProductRel_coordinateSwap (AssociativeParameters.Construction.lineAssociativeRelation12 B C)
  have h₂₃ := AssociativityCoordinateSwap.Construction.horizontalProductRel_coordinateSwap (AssociativeParameters.Construction.lineAssociativeRelation23 B C)
  have h₁₂₃ := AssociativityCoordinateSwap.Construction.horizontalProductRel_coordinateSwap (AssociativeParameters.Construction.lineAssociativeRelation1_23 B C)
  have h₁₂₃' := AssociativityCoordinateSwap.Construction.horizontalProductRel_coordinateSwap (AssociativeParameters.Construction.lineAssociativeRelation12_3 B C)
  have hg := GroupAssociativity.Construction.picardImageVerticalGroupProduct_associative D βv hβv βh hβh q i hfac x₀ y₀ z₀ xy₀ yz₀ w₀ h₁₂ h₂₃ h₁₂₃ h₁₂₃'
  have hp := FiberAssociativity.Construction.fiberBilinear_associative_pullback (L) r
    x₀ y₀ z₀ xy₀ yz₀ w₀ x y z xy yz w hx hy hz hxy' hyz' hw
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac y₀ z₀ yz₀ h₂₃) (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x₀ yz₀ w₀ h₁₂₃)
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x₀ y₀ xy₀ h₁₂) (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac xy₀ z₀ w₀ h₁₂₃') hg U m n p
  rw [ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac r x₀ yz₀ w₀ h₁₂₃ x yz w hxw hx hyz' hw,
    ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac r y₀ z₀ yz₀ h₂₃ y z yz hyz hy hz hyz',
    ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac r xy₀ z₀ w₀ h₁₂₃' xy z w hzw hxy' hz hw,
    ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac r x₀ y₀ xy₀ h₁₂ x y xy hxy hx hy hxy'] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.VerticalAssociativity.Construction
