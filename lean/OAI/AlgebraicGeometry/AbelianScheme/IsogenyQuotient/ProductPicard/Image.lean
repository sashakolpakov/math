import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.FiniteKernel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Scheme

/-! # Image -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.Image.Construction

noncomputable section

/-! Quotient the original abelian variety by the constructed finite
Picard kernel. The resulting abelian variety has exactly the fibres of
the original Picard homomorphism; no surjectivity onto the whole Picard
sheaf or dual representability is asserted here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
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

theorem exists_productPicard_image_quotient (hample : (RigidifiedPicardKernelFinite.Construction.rigidifiedDiagonalLine D).IsAmple) :
    ∃ (C : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of k))) (q : B ⟶ C.toOver),
      IsMonHom q ∧ Quotients.FiniteDescent.AbelianQuotient.Construction.FiniteLocallyFree q.left ∧ Surjective q.left ∧
      ∀ (T : Over (Spec (.of k))) (x : T ⟶ B),
        x ≫ q = 1 ↔ SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T x = 1 := by
  let B' : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of k)) := { toOver := B }
  let : GrpObj D.zeroSchemeOver := FiniteKernel.Construction.productPicardKernelGroup D βv hβv βh hβh
  have : IsMonHom D.zeroInclusion := FiniteKernel.Construction.productPicardKernelInclusion_isMonHom D βv hβv βh hβh
  have : IsFinite D.zeroSchemeOver.hom := FiniteKernel.Construction.productPicardKernel_finite D βv hβv βh hβh hample
  obtain ⟨C, q, hq, hfin, hsurj, hk, _hu⟩ :=
    Quotients.FiniteDescent.Scheme.Construction.exists_abelian_scheme_quotient (Spec (.of k)) B' D.zeroSchemeOver D.zeroInclusion
      (FiniteKernel.Construction.productPicardKernel_closed D βv hβv βh hβh) ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨C, q, hq, hfin, hsurj, fun T x =>
    (hk T x).trans (FiniteKernel.Construction.productPicardKernel_full_kernel D βv hβv βh hβh T x).symm⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.Image.Construction
