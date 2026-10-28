import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.AmpleFiberPowerSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FieldProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.PointwiseProjectivity

/-! # Noetherian Affine Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every polarized full-level abelian object over a Noetherian affine base has an ample canonical graph bundle and an actual projective presentation. Global power sections are constructed from proper-flat fiber lifting. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}}
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem Polarized.NoetherianAffineProjectivity.PolarizedAbelianWithLevel.graphBundle_isAmple_residueFiber (x : S) :
    (A.graphBundle.pullback (A.abelian.scheme.hom.fiberι x)).IsAmple :=
  (A.pullback (S.fromSpecResidueField x)).graphBundle_isAmple_overField.of_iso
    (A.graphBundle_baseChangeIso (S.fromSpecResidueField x))

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_pointwise_power_sections_of_noetherian_affine :
    ∀ y : A.abelian.scheme.left, ∃ (d : ℕ) (_ : 0 < d)
      (s : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower d).sheaf),
        y ∈ Ample.LineBundles.sectionNonvanishing s :=
  ProperFlat.AmpleFiberPowerSections.properFlat_pointwise_power_sections_of_ample_fibers A.abelian.scheme.hom A.graphBundle
    (Polarized.NoetherianAffineProjectivity.PolarizedAbelianWithLevel.graphBundle_isAmple_residueFiber A)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_isAmple_of_noetherian_affine : A.graphBundle.IsAmple :=
  A.graphBundle_isAmple_iff_pointwise_power_sections.mpr
    A.graphBundle_pointwise_power_sections_of_noetherian_affine

def PolarizationData.PolarizedAbelianWithFullLevel.projectivePresentation_of_noetherian_affine : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme :=
  A.graphBundle_isAmple_of_noetherian_affine.projectivePresentation A.abelian.scheme.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
