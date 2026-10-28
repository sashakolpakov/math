import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv

/-! # Parameter Class Equality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.ParameterClassEquality

noncomputable section

/-! Equality in the relative Picard sheaf of a normalized parameter
family is equality of the actual line-bundle classes on each quasicompact,
quasiseparated test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) {P : Over (Spec (.of k))}
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (e : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    {T : Over (Spec (.of k))} [CompactSpace T.left] [QuasiSeparatedSpace T.left]

include e

theorem parameterPicard_eq_iff_lineClass_eq (x y : T ⟶ P) :
    ParameterizedPicardClass.parameterPicardClass Q x = ParameterizedPicardClass.parameterPicardClass Q y ↔
      ParameterizedPicardClass.parameterLineClass Q x = ParameterizedPicardClass.parameterLineClass Q y := by
  constructor
  · intro h
    have H := AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_eq_of_picard_eq A (ParameterizedPicardClass.parameterLineClass Q x) (ParameterizedPicardClass.parameterLineClass Q y) h
    rw [AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_eq_self A T _ (ParameterizedPicardClass.parameterLineClass_normalized Q e x),
      AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_eq_self A T _ (ParameterizedPicardClass.parameterLineClass_normalized Q e y)] at H
    exact H
  · exact congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T))

theorem parameterPicard_eq_iff_lineIso (x y : T ⟶ P) :
    ParameterizedPicardClass.parameterPicardClass Q x = ParameterizedPicardClass.parameterPicardClass Q y ↔
      Nonempty ((Q.pullback (x ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
        (Q.pullback (y ⊗ₘ 𝟙 A.scheme).left).sheaf) := by
  rw [parameterPicard_eq_iff_lineClass_eq A Q e]
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (x ⊗ₘ 𝟙 A.scheme).left) =
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (y ⊗ₘ 𝟙 A.scheme).left) ↔ _
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.ParameterClassEquality
