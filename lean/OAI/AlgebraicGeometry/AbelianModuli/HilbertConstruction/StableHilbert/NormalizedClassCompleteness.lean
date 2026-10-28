import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ZeroNormalizedBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.SpectrumLineBundleFrames

/-! # Normalized Class Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedClassCompleteness.StableHilbertCoverage

noncomputable section

/-! Transport the actual normalized graph class under base change and
compare section ranks over a field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem zeroNormalized_class_congr
    {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (L M : Line.Bundles.LineBundle A.scheme.left)
    (h : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M) :
    Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle L) =
      Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle M) :=
  (Line.Bundles.LineBundle.classOf_sectionNormalized A.scheme.hom η[A.scheme].left L).trans
    ((congrArg (Line.Bundles.LineBundle.sectionNormalizeClass A.scheme.hom η[A.scheme].left) h).trans
      (Line.Bundles.LineBundle.classOf_sectionNormalized A.scheme.hom η[A.scheme].left M).symm)

theorem normalizedGraphPowerClass_baseChange
    {S T : Scheme.{u}} {g N d : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme)
    (h : Line.Bundles.LineBundle.classOf (A.abelian.zeroNormalizedBundle P.ampleLineBundle) =
      Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d)) (f : T ⟶ S) :
    Line.Bundles.LineBundle.classOf ((A.pullback f).abelian.zeroNormalizedBundle (P.baseChange f).ampleLineBundle) =
      Line.Bundles.LineBundle.classOf ((A.pullback f).graphBundle.tensorPower d) := by
  let π := pullback.fst A.abelian.scheme.hom f
  let B := A.pullback f
  have hL := zeroNormalized_class_congr B.abelian (P.baseChange f).ampleLineBundle
    (P.ampleLineBundle.pullback π) (Quotient.sound ⟨P.baseChangeTwistingBundleIso f⟩)
  have hn : Line.Bundles.LineBundle.classOf ((A.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback π) =
      Line.Bundles.LineBundle.classOf (B.abelian.zeroNormalizedBundle (P.ampleLineBundle.pullback π)) :=
    Quotient.sound ⟨A.abelian.zeroNormalizedBundle_baseChangeIso P.ampleLineBundle f⟩
  have hG : Line.Bundles.LineBundle.classOf ((A.graphBundle.tensorPower d).pullback π) =
      Line.Bundles.LineBundle.classOf (B.graphBundle.tensorPower d) :=
    Quotient.sound ⟨A.graphBundle.powerBaseChangeIso π d ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left d).mapIso (A.graphBundle_baseChangeIso f).symm⟩
  exact hL.trans (hn.symm.trans ((congrArg (Line.Bundles.LineBundle.pullbackClass π) h).trans hG))

theorem normalizedLineBundle_sections_finrank_eq
    {K : Type u} [Field K] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (L M : Line.Bundles.LineBundle A.scheme.left)
    (h : Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle L) = Line.Bundles.LineBundle.classOf M) :
    Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.scheme.hom).obj L.sheaf) =
      Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.scheme.hom).obj M.sheaf) := by
  let e₀ : (A.zeroNormalizedBundle L).sheaf ≅ L.sheaf :=
    Line.Bundles.LineBundle.sectionNormalized_fixedIso A.scheme.hom η[A.scheme].left L
      (Local.SpectrumLineBundleFrames.localSpectrum_lineBundle_trivial (L.pullback η[A.scheme].left))
  let e₁ : (A.zeroNormalizedBundle L).sheaf ≅ M.sheaf := (Quotient.exact h).some
  exact (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso A.scheme.hom (e₀.symm ≪≫ e₁)).finrank_eq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedClassCompleteness.StableHilbertCoverage
