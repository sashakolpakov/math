import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.RelativeValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPicardKernelFinite

/-! # Finite Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.FiniteKernel.Construction

noncomputable section

/-! The actual homogeneous Picard homomorphism associated with a
rigidified product line has a represented full kernel. When the diagonal
is ample, that kernel is finite; its group structure and universal
property are constructed without a represented Picard target. -/

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

@[instance_reducible]
def productPicardKernelGroup : GrpObj D.zeroSchemeOver :=
  (D.zeroGroupData (RelativeValue.Construction.productPicard_zeroIsSubgroup D βv hβv βh hβh)).group

theorem productPicardKernelInclusion_isMonHom :
    letI := productPicardKernelGroup D βv hβv βh hβh
    IsMonHom D.zeroInclusion :=
  (D.zeroGroupData (RelativeValue.Construction.productPicard_zeroIsSubgroup D βv hβv βh hβh)).monHom

theorem productPicardKernel_full_kernel (T : Over (Spec (.of k))) (x : T ⟶ B) :
    SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh T x = 1 ↔
      ∃! z : T ⟶ D.zeroSchemeOver, z ≫ D.zeroInclusion = x := by
  rw [RelativeValue.Construction.productPicard_zero_iff D βv hβv βh hβh, D.zeroInclusion_factorization]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz, fun w hw => (cancel_mono D.zeroInclusion).mp (hw.trans hz.symm)⟩
  · rintro ⟨z, hz, _⟩
    exact ⟨z, hz⟩

include βv hβv βh hβh in
theorem productPicardKernel_closed : IsClosedImmersion D.zeroInclusion.left :=
  D.zeroScheme_closed (RelativeValue.Construction.productPicard_zeroIsSubgroup D βv hβv βh hβh)

include βv hβv βh hβh in
theorem productPicardKernel_finite (hample : (RigidifiedPicardKernelFinite.Construction.rigidifiedDiagonalLine D).IsAmple) :
    IsFinite D.zeroSchemeOver.hom :=
  RigidifiedPicardKernelFinite.Construction.rigidifiedPicardKernel_isFinite D (RelativeValue.Construction.productPicard_zeroIsSubgroup D βv hβv βh hβh) hample

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.FiniteKernel.Construction
