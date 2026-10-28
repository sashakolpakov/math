import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.RelativeZeroTriviality

/-! # Rigidified Bundle Relative Zero -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedBundleRelativeZero.Construction

noncomputable section

/-! A normalized actual bundle with zero relative class is trivial.
The parameter is locally noetherian and the group is geometrically integral. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  {T : Over (Spec (.of k))} [IsLocallyNoetherian T.left]

theorem rigidifiedBundle_class_trivial_of_relative_zero
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left)
    (e : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left := by
  let R : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A T := ⟨L, e⟩
  have hid : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (R.line (𝟙 T)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 T) ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = _
    rw [tensorHom_id, id_whiskerRight, Over.id_left]
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _
  apply hid.symm.trans
  apply R.class_trivial_of_relative_zero (𝟙 T)
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (R.line (𝟙 T))) = _
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T)) hid).trans h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedBundleRelativeZero.Construction
