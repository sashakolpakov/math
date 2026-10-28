import OAI.RepresentationTheory.Theta.Geometric.Picard.OpenCoverEquality

/-! # Base Twists -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.BaseTwists

noncomputable section

/-! Tensoring by a line bundle from the test base does not change the
actual sheafified relative Picard class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

theorem parameterBaseClass_naturality {S : Scheme.{u}} (A : Over S)
    {T U : Over S} (f : U ⟶ T) (r : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) :
    PicardPullback.picardPullback (f ⊗ₘ 𝟙 A).left (PicardPullback.picardPullback (fst T A).left r) =
      PicardPullback.picardPullback (fst U A).left (PicardPullback.picardPullback f.left r) := by
  rw [PicardPullback.picardPullback_comp, PicardPullback.picardPullback_comp]
  exact congrArg (fun h => PicardPullback.picardPullback h r) (congrArg Over.Hom.left (tensorHom_fst f (𝟙 A)))

theorem relativePicard_tensor_base {S : Scheme.{u}} (A T : Over S)
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) (r : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (q * PicardPullback.picardPullback (fst T A).left r) =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) q := by
  refine Quotient.inductionOn r (fun L => ?_)
  choose O hx he using L.locallyTrivial
  have hO : iSup O = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  let V := T.left.openCoverOfIsOpenCover O hO
  apply OpenCoverEquality.relativePicard_eq_of_openCover A T V
  intro i
  have hi : PicardPullback.picardPullback (OpenCoverEquality.coverOverMap T V i).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 :=
    Quotient.sound (he i)
  change PicardPullback.picardPullback (OpenCoverEquality.coverOverMap T V i ⊗ₘ 𝟙 A).left
      (q * PicardPullback.picardPullback (fst T A).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
    PicardPullback.picardPullback (OpenCoverEquality.coverOverMap T V i ⊗ₘ 𝟙 A).left q
  rw [map_mul, parameterBaseClass_naturality, hi, map_one, mul_one]

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.BaseTwists
