import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.Image
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Image

/-! # Abelian Image -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.AbelianImage.Construction

noncomputable section

/-! The abelian quotient by the actual finite Picard kernel embeds
into the homogeneous Picard sheaf, with an exact factorization of the
original product-line map. Surjectivity onto the whole sheaf remains
a separate assertion. -/

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

include βh hβh in
theorem exists_productPicard_abelian_image (hample : (RigidifiedPicardKernelFinite.Construction.rigidifiedDiagonalLine D).IsAmple) :
    ∃ (C : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of k))) (q : B ⟶ C.toOver)
      (i : uliftYoneda.{u + 1}.obj C.toOver ⟶
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj),
      IsMonHom q ∧ Quotients.FiniteDescent.AbelianQuotient.Construction.FiniteLocallyFree q.left ∧ Surjective q.left ∧
        Mono i ∧ uliftYoneda.map q ≫ i = SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv := by
  obtain ⟨C, q, hq, hfin, hsurj, hk⟩ := Image.Construction.exists_productPicard_image_quotient D βv hβv βh hβh hample
  have : IsMonHom q := hq
  have : Flat q.left := hfin.2.1
  have : Surjective q.left := hsurj
  have : LocallyOfFinitePresentation q.left := hfin.2.2
  have hfibres (T : Over (Spec (.of k))) (x y : T ⟶ B) :
      (SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv).app (op T) (ULift.up x) =
        (SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv).app (op T) (ULift.up y) ↔
        x ≫ q = y ≫ q := by
    change SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T x =
      SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T y ↔ _
    have h := hk T (x * y⁻¹)
    rw [MonObj.mul_comp, GrpObj.inv_comp, map_mul, map_inv, mul_inv_eq_one, mul_inv_eq_one] at h
    exact h.symm
  obtain ⟨i, hi, hpi⟩ := Sheaf.Image.Construction.exists_mono_sheaf_factor_of_fibres q
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B)
    (SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv) hfibres
  exact ⟨C, q, i, hq, hfin, hsurj, hi, hpi⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.AbelianImage.Construction
