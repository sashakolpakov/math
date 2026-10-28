import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceFiberTriviality
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceBaseChangeValues

/-! # Difference Fiber Homogeneity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceFiberHomogeneity.Geometric

noncomputable section

/-! Triviality of the original difference bundle on a field fiber
implies the original homogeneous line-class predicate on that fiber.
The proof uses the actual pullback lift and Picard base-change equivalence. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem homogeneous_fieldFiber_of_difference_trivial
    {k : Type} [Field k] (f : Spec (.of k) ⟶ S)
    (e : ((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).pullback
      (pullback.fst (A.scheme ⊗ A.scheme).hom f)).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback f).obj (A.scheme ⊗ A.scheme)).left) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (A.pullback f)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom f))) := by
  let B := A.pullback f
  let M := L.pullback (pullback.fst A.scheme.hom f)
  let U := B.scheme
  let V := (Over.map f).obj U
  let a := A.baseChangePointsEquiv f U (𝟙 B.scheme)
  let φ : (V ⊗ A.scheme).left ⟶ (A.scheme ⊗ A.scheme).left := (a ⊗ₘ 𝟙 A.scheme).left
  let ρ : (V ⊗ A.scheme).left ⟶ Spec (.of k) := (fst V A.scheme).left ≫ U.hom
  have hφ : φ ≫ (A.scheme ⊗ A.scheme).hom = ρ ≫ f := by
    have h : φ ≫ (A.scheme ⊗ A.scheme).hom = (fst V A.scheme).left ≫ (U.hom ≫ f) :=
      (a ⊗ₘ 𝟙 A.scheme).w
    exact h.trans (Category.assoc _ _ _).symm
  let r := pullback.lift φ ρ hφ
  let j := pullback.fst (A.scheme ⊗ A.scheme).hom f
  have hr : r ≫ j = φ := pullback.lift_fst _ _ _
  let d : ((RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).line a).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (V ⊗ A.scheme).left :=
    (Scheme.Modules.pullbackCongr hr.symm).app (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf ≪≫
      ((Scheme.Modules.pullbackComp r j).app (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf).symm ≪≫
      (Scheme.Modules.pullback r).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso r
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).line a) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (V ⊗ A.scheme).left := Quotient.sound ⟨d⟩
  have hz : (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme V :=
    congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op V)) hc
  have hb : (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference B M).relativeValue (𝟙 B.scheme) =
      AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass B.scheme U := by
    apply (AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f U).injective
    exact (DifferenceBaseChangeValues.Geometric.relativeDifference_value_baseChange A L f U (𝟙 B.scheme)).trans
      (hz.trans (AbelianModuli.HilbertConstruction.Picard.BaseChange.trivialPicardClass_baseChange A.scheme f U).symm)
  apply (DifferenceTrivialityHomogeneity.Geometric.difference_trivial_iff_homogeneous_line B M).mp
  exact DifferenceTrivialityHomogeneity.Geometric.difference_trivial_of_identity_translation B M
    ((ReferenceLineTranslation.Geometric.relativeDifference_zero_iff_originalTranslation B M (𝟙 B.scheme)).mp hb)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceFiberHomogeneity.Geometric
