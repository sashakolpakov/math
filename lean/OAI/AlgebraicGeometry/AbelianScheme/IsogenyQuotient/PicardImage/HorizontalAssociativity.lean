import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameterFactors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupAssociativity

/-! # Horizontal Associativity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.HorizontalAssociativity.Construction

noncomputable section

/-! The image horizontal product is associative on all test schemes,
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

theorem picardImageHorizontalProduct_associative {T : Over (Spec (.of k))}
    (x y z xy yz w : T ⟶ C ⊗ B)
    (hxy : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) x y xy)
    (hyz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) y z yz)
    (hxw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) x yz w)
    (hzw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) xy z w)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U))
    (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) z, U)) :
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x yz w hxw).app U m ((GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac y z yz hyz).app U n p) =
      (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac xy z w hzw).app U ((GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x y xy hxy).app U m n) p := by
  let x₀ := AssociativeParameters.Construction.lineAssociativePoint1 C B
  let y₀ := AssociativeParameters.Construction.lineAssociativePoint2 C B
  let z₀ := AssociativeParameters.Construction.lineAssociativePoint3 C B
  let xy₀ := AssociativeParameters.Construction.lineAssociativePoint12 C B
  let yz₀ := AssociativeParameters.Construction.lineAssociativePoint23 C B
  let w₀ := AssociativeParameters.Construction.lineAssociativePoint123 C B
  let r := AssociativeParameterFactors.Construction.lineAssociativeParameterLift x y z
  have hx : r ≫ x₀ = x := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point1 x y z
  have hy : r ≫ y₀ = y := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point2 x y z hxy.2.1
  have hz : r ≫ z₀ = z := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point3 x y z (hxy.2.1.trans hyz.2.1)
  have hxy' : r ≫ xy₀ = xy := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point12 x y z xy hxy
  have hyz' : r ≫ yz₀ = yz := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point23 x y z yz hxy.2.1 hyz
  have hw : r ≫ w₀ = w := AssociativeParameterFactors.Construction.lineAssociativeParameterLift_point123 x y z xy w hxy hzw
  have h₁₂ := AssociativeParameters.Construction.lineAssociativeRelation12 C B
  have h₂₃ := AssociativeParameters.Construction.lineAssociativeRelation23 C B
  have h₁₂₃ := AssociativeParameters.Construction.lineAssociativeRelation1_23 C B
  have h₁₂₃' := AssociativeParameters.Construction.lineAssociativeRelation12_3 C B
  have hg := GroupAssociativity.Construction.picardImageHorizontalGroupProduct_associative D βv hβv βh hβh q i hfac x₀ y₀ z₀ xy₀ yz₀ w₀ h₁₂ h₂₃ h₁₂₃ h₁₂₃'
  have hp := FiberAssociativity.Construction.fiberBilinear_associative_pullback (L) r
    x₀ y₀ z₀ xy₀ yz₀ w₀ x y z xy yz w hx hy hz hxy' hyz' hw
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac y₀ z₀ yz₀ h₂₃) (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x₀ yz₀ w₀ h₁₂₃)
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x₀ y₀ xy₀ h₁₂) (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac xy₀ z₀ w₀ h₁₂₃') hg U m n p
  rw [ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac r x₀ yz₀ w₀ h₁₂₃ x yz w hxw hx hyz' hw,
    ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac r y₀ z₀ yz₀ h₂₃ y z yz hyz hy hz hyz',
    ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac r xy₀ z₀ w₀ h₁₂₃' xy z w hzw hxy' hz hw,
    ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac r x₀ y₀ xy₀ h₁₂ x y xy hxy hx hy hxy'] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.HorizontalAssociativity.Construction
