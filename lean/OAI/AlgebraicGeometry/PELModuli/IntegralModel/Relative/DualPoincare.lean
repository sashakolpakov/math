import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.NormalizedPicardInjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareBaseChange

/-! # Dual Poincare -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualPoincare

noncomputable section

/-! The constructed dual morphism has the actual Poincare line-bundle
identity for varying abelian families over reduced noetherian bases. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem dualPicardPullback_actual_poincare_relative
    {S : Scheme.{0}} [IsReduced S] [IsNoetherian S] {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f ⊗ₘ 𝟙 A.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) := by
  have : GeometricallyReduced DB.abelian.scheme.hom :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth DB.abelian.scheme.hom
  let : IsReduced DB.abelian.scheme.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian DB.abelian.scheme.hom
  let : IsLocallyNoetherian DB.abelian.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian DB.abelian.scheme.hom
  let : CompactSpace DB.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace DB.abelian.scheme.hom
  let : IsNoetherian DB.abelian.scheme.left := ⟨⟩
  exact NormalizedPicardInjection.RelativeNormalizedPicard.class_eq_of_picard_eq A _ _
    (DualPoincareBaseChange.dualPicardPullback_normalized_left DA DB f)
    (DualPoincareBaseChange.dualPicardPullback_normalized_right DB f)
    (DualPoincareBaseChange.dualPicardPullback_actual_classes_in_picard DA DB f)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualPoincare
