import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafMap
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.PicardHomKernel

/-! # Relative Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.RelativeValue.Construction

noncomputable section

/-! The constructed homogeneous Picard homomorphism has exactly the
relative Picard value of the original rigidified product line. Its
scheme-valued zero condition is therefore a subgroup on every test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard

universe u
variable {k : Type u} [Field k] {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B A))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B A))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B A)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B A))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B A))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B A)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

theorem productPicard_relativeValue {T : Over (Spec (.of k))} (x : T ⟶ B) :
    Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom A T
      (SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T x) =
      D.relativeValue x := by
  rw [Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.homogeneousPicardSheafInclusion_toSheafify A) (op T))
    (SheafMap.Construction.productNativeHomogeneousClass (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv x)

theorem productPicard_zero_iff {T : Over (Spec (.of k))} (x : T ⟶ B) :
    SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T x = 1 ↔
      D.relativeValue x = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  let f := Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom A T
  have hf : Function.Injective f := by
    have hm : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op T)) := inferInstance
    intro a b hab
    apply (CategoryTheory.mono_iff_injective _).mp hm
    change Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom A T a =
      Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom A T b at hab
    simpa only [Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply] using hab
  constructor
  · intro h
    rw [← productPicard_relativeValue D βv hβv βh hβh x, h, map_one,
      Picard.Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one]
  · intro h
    apply hf
    change Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom A T _ = Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom A T 1
    rw [productPicard_relativeValue, h, map_one, Picard.Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one]

include βv hβv βh hβh in
theorem productPicard_zeroIsSubgroup : D.ZeroIsSubgroup := by
  constructor
  · intro T
    exact (productPicard_zero_iff D βv hβv βh hβh (1 : T ⟶ B)).mp (map_one _)
  · intro T a b ha hb
    apply (productPicard_zero_iff D βv hβv βh hβh (a * b)).mp
    rw [map_mul, (productPicard_zero_iff D βv hβv βh hβh a).mpr ha,
      (productPicard_zero_iff D βv hβv βh hβh b).mpr hb, one_mul]
  · intro T a ha
    apply (productPicard_zero_iff D βv hβv βh hβh a⁻¹).mp
    rw [map_inv, (productPicard_zero_iff D βv hβv βh hβh a).mpr ha, inv_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.RelativeValue.Construction
