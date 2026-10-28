import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Complement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleAffinePullback

/-! # Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Projectivity

noncomputable section

/-! Projectivity of the original dual scheme follows from the actual
complementary polarization isogeny and pullback of the ample bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem dual_has_ample_line_bundle :
    ∃ L : HilbertConstruction.Line.Bundles.LineBundle A.dual.abelian.scheme.left, L.IsAmple := by
  obtain ⟨_, _, q, _, hfin, _, _, _, _⟩ := Polarization.Complement.exists_polarization_complement A
  let : IsFinite q.left := hfin
  let : CompactSpace A.dual.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.dual.abelian.scheme.hom
  exact ⟨(Intrinsic.ChernPairing.polarizationLineBundle A).pullback q.left,
    AmpleAffinePullback.ample_pullback_affine q.left (Intrinsic.ChernPairing.polarizationLineBundle A) (Intrinsic.ChernPairing.polarizationLineBundle_ample A)⟩

def dualProjectivePresentation : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme := by
  let L := Classical.choose (dual_has_ample_line_bundle A)
  have hL : L.IsAmple := Classical.choose_spec (dual_has_ample_line_bundle A)
  exact hL.projectivePresentation A.dual.abelian.scheme.hom

def dualNativeProjectivePresentation :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation A.dual.abelian.scheme.left A.dual.abelian.scheme.hom :=
  Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation (dualProjectivePresentation A)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Projectivity
