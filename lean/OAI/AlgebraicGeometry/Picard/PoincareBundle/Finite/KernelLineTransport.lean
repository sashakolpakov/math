import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.LineTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupLineFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PositiveFormula

/-! # Kernel Line Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.KernelLineTransport

noncomputable section

/-! A finite killed subgroup gives actual translation isomorphisms for an ample inducing line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

variable {k : Type u} [Field k] {H A Z : Over (Spec (.of k))}
  [GrpObj H] [IsCommMonObj H] [IsFinite H.hom] [GrpObj A] [GrpObj Z]
  (i : H ⟶ A) (φ : A ⟶ Z) (hi : i ≫ φ = 1)
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (normalized : (Scheme.Modules.pullback (Poincare.KernelTrivialization.zeroSection (Z := Z) (X := A)).left).obj P.sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)

include hi normalized

/-- Both the ample line and its global subgroup-translation isomorphism are constructed. -/
theorem exists_ample_translation
    (h : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A ((Line.Comparison.Bundle.toShared P).pullback (φ ⊗ₘ 𝟙 A).left)) :
    ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left,
      L.IsAmple ∧ Nonempty ((L.pullback η[A].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) ∧
      Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine P φ).sheaf (L.pullback (fst A A).left).sheaf)
        (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf) ∧
      Nonempty ((L.pullback (snd H A).left).sheaf ≅
        (L.pullback (((i ⊗ₘ 𝟙 A) ≫ μ[A]).left)).sheaf) := by
  obtain ⟨L, hL, hzero, ⟨formula⟩⟩ := h
  obtain ⟨s⟩ := GroupLineFrame.exists_frame k H (Line.Comparison.Bundle.fromShared (L.pullback i.left))
  exact ⟨L, hL, hzero, ⟨formula⟩, ⟨Kernel.LineTransport.translationIso i φ hi P normalized L formula s.symm⟩⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.KernelLineTransport
