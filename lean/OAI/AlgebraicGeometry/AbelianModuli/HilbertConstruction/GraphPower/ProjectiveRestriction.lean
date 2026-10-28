import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting

/-! # Projective Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.ProjectiveRestriction

noncomputable section

/-! The original normalized projective-line enhancement commutes with
restriction, using the native projective presentation on the new base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

theorem projectiveGraphPowerEnhancement_baseChange_comp_iff
    {S U T : Scheme.{u}} {g N : ℕ} (δ : Fin g → ℕ)
    (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme) (d : ℕ)
    (i : U ⟶ S) (t : T ⟶ U) :
    Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback (t ≫ i))
      ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
        (pullback.fst F.abelian.scheme.hom (t ≫ i))) d) ↔
      Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ ((F.pullback i).pullback t)
        (((F.abelian.pullback i).zeroNormalizedBundle (P.baseChange i).ampleLineBundle).pullback
          (pullback.fst (F.abelian.pullback i).scheme.hom t)) d) := by
  let A := F.abelian.pullback i
  let L := P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom i)
  let M := (P.baseChange i).ampleLineBundle
  have h : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M :=
    Quotient.sound ⟨(P.baseChangeTwistingBundleIso i).symm⟩
  have hn : Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle L) =
      Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle M) :=
    (Line.Bundles.LineBundle.classOf_sectionNormalized A.scheme.hom η[A.scheme].left L).trans
      ((congrArg (Line.Bundles.LineBundle.sectionNormalizeClass A.scheme.hom η[A.scheme].left) h).trans
        (Line.Bundles.LineBundle.classOf_sectionNormalized A.scheme.hom η[A.scheme].left M).symm)
  let e : (A.zeroNormalizedBundle L).sheaf ≅ (A.zeroNormalizedBundle M).sheaf :=
    Classical.choice (Quotient.exact hn)
  exact (EnhancementRestriction.normalizedGraphPowerEnhancement_baseChange_comp_iff δ F P.ampleLineBundle d i t).trans
    (EnhancementRestriction.graphPowerEnhancement_nonempty_iff_of_bundleIso δ ((F.pullback i).pullback t) _ _ d
      ((Scheme.Modules.pullback (pullback.fst A.scheme.hom t)).mapIso e))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.ProjectiveRestriction
