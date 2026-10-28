import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProperFiberAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ResidueFiberAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PullbackAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FiberProjectivity

/-! # Arbitrary Base Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The original geometric positivity of a polarized abelian scheme
makes its graph bundle relatively ample over every base scheme. No
Noetherian or reducedness condition is imposed on the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_isAmple_of_affine [IsAffine S] : A.graphBundle.IsAmple := by
  let f := S.isoSpec.inv
  let B := A.pullback f
  have hB : B.graphBundle.IsAmple :=
    Smooth.ProperFiberAmpleness.smoothProper_isAmple_of_fiberwise B.abelian.scheme B.graphBundle
      (Polarized.ResidueFiberAmpleness.PolarizedAbelianWithLevel.graphBundle_isAmple_residueFiber B)
  have h : (A.graphBundle.pullback (pullback.fst A.abelian.scheme.hom f)).IsAmple :=
    hB.of_iso (A.graphBundle_baseChangeIso f)
  exact (Line.Bundles.LineBundle.isAmple_pullback_iff_of_isIso (L := A.graphBundle)
    (pullback.fst A.abelian.scheme.hom f)).mp h

def PolarizationData.PolarizedAbelianWithFullLevel.projectivePresentation_of_affine [IsAffine S] :
    Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme :=
  A.graphBundle_isAmple_of_affine.projectivePresentation A.abelian.scheme.hom

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_isRelativelyAmple :
    A.graphBundle.IsRelativelyAmple A.abelian.scheme.hom := by
  intro U hU
  have : IsAffine U.toScheme := hU
  have h := (A.pullback U.ι).graphBundle_isAmple_of_affine
  exact (A.graphBundle.isAmple_pullback_iff_cartesian
    (isPullback_morphismRestrict A.abelian.scheme.hom U).flip).mpr
      (h.of_iso (A.graphBundle_baseChangeIso U.ι))

def PolarizationData.PolarizedAbelianWithFullLevel.localProjectivePresentation
    (U : S.Opens) (hU : IsAffineOpen U) :
    Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (A.abelian.scheme.hom ∣_ U)) :=
  A.graphBundle_isRelativelyAmple.localProjectivePresentation U hU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
