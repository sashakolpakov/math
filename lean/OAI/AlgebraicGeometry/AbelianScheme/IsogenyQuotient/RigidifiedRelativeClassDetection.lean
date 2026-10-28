import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.RelativeZeroTriviality
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId
import OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup

/-! # Rigidified Relative Class Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedRelativeClassDetection.Construction

noncomputable section

/-! Relative Picard equality detects actual line-bundle classes with
fixed identity-axis frames over a locally noetherian parameter scheme.
This applies to the product families used in the Picard image construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  {T : Over (Spec (.of k))} [IsLocallyNoetherian T.left]
  (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left)
  (eL : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
  (eM : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)

include eL eM in
set_option backward.isDefEq.respectTransparency false in
theorem rigidified_class_eq_of_relative_class_eq
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M := by
  let c := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L / AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M
  let N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left := c.out
  have hN : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N = c := Quotient.out_eq c
  have haxis : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass T.left := by
    rw [hN]
    change Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (lift (𝟙 T) (1 : T ⟶ A)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L / AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) = 1
    rw [map_div]
    have hl : Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (lift (𝟙 T) (1 : T ⟶ A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 :=
      Quotient.sound ⟨eL⟩
    have hm : Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (lift (𝟙 T) (1 : T ⟶ A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) = 1 :=
      Quotient.sound ⟨eM⟩
    rw [hl, hm]
    exact div_self' _
  let R : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A T := ⟨N, Classical.choice (Quotient.exact haxis)⟩
  have hid : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (R.line (𝟙 T)) = c := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 T) ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N) = c
    rw [tensorHom_id, id_whiskerRight, Over.id_left]
    exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N)).trans hN
  have hz : R.relativeValue (𝟙 T) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
    change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (R.line (𝟙 T))) = _
    rw [hid, Picard.Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one]
    change Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L / AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) = 1
    rw [map_div]
    change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) /
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) = 1
    rw [h]
    exact div_self' _
  have hc : c = 1 := hid.symm.trans (R.class_trivial_of_relative_zero (𝟙 T) hz)
  exact div_eq_one.mp hc

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedRelativeClassDetection.Construction
