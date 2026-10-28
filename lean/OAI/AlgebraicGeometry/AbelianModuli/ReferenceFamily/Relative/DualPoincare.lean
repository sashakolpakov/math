import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.NormalizedPicardInjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareBaseChange

/-! # Dual Poincare -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualPoincare

noncomputable section

/-! The constructed dual morphism has the actual Poincare line-bundle
identity for varying abelian families over noetherian bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareBaseChange

theorem dualPicardPullback_actual_poincare_relative
    {S : Scheme.{0}} [IsNoetherian S] {g h : ℕ}
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f ⊗ₘ 𝟙 A.scheme).left
        (HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left
        (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) := by
  let : IsLocallyNoetherian DB.abelian.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian DB.abelian.scheme.hom
  let : CompactSpace DB.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace DB.abelian.scheme.hom
  let : IsNoetherian DB.abelian.scheme.left := ⟨⟩
  exact NormalizedPicardInjection.RelativeNormalizedPicard.class_eq_of_picard_eq A _ _
    (PELModuli.IntegralModel.DualPoincareBaseChange.dualPicardPullback_normalized_left DA DB f)
    (PELModuli.IntegralModel.DualPoincareBaseChange.dualPicardPullback_normalized_right DB f)
    (PELModuli.IntegralModel.DualPoincareBaseChange.dualPicardPullback_actual_classes_in_picard DA DB f)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualPoincare
