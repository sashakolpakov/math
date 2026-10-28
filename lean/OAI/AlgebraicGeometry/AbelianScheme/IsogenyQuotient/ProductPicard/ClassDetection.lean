import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.FiniteKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafKernel

/-! # Class Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ClassDetection.Construction

noncomputable section

/-! For the fixed rigidified family, equality of its homogeneous
Picard-sheaf values is already equality of the actual family line
classes, on arbitrary test schemes. This supplies effective family
descent along the constructed abelian image quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
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

theorem productPicard_zero_iff_actual_class {T : Over (Spec (.of k))} (x : T ⟶ B) :
    SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T x = 1 ↔
      SheafMap.Construction.productNativeHomogeneousClass (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv x = 1 := by
  rw [RelativeValue.Construction.productPicard_zero_iff D βv hβv βh hβh, D.relative_zero_iff_class_trivial]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

theorem productPicard_eq_iff_class_eq {T : Over (Spec (.of k))} (x y : T ⟶ B) :
    SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T x =
      SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T y ↔
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line x) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line y) := by
  constructor
  · intro h
    have hz : SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have hc := (productPicard_zero_iff_actual_class D βv hβv βh hβh (x * y⁻¹)).mp hz
    change SheafMap.Construction.productNativeHomogeneousClassHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T (x * y⁻¹) = 1 at hc
    rw [map_mul, map_inv, mul_inv_eq_one] at hc
    exact congrArg Subtype.val hc
  · intro h
    have hc : SheafMap.Construction.productNativeHomogeneousClass (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv x =
        SheafMap.Construction.productNativeHomogeneousClass (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv y := Subtype.ext h
    exact congrArg ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).app (op T)) hc

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ClassDetection.Construction
