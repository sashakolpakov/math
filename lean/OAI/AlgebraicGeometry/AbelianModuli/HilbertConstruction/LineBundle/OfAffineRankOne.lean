import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RankOneLocalFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionFrameImage

/-! # Of Affine Rank One -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.OfAffineRankOne

noncomputable section

/-! Finite flat rank-one section modules on affine restrictions construct a line bundle on an arbitrary scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]

def lineBundleOfAffineRankOne
    (h : ∀ U : X.Opens, IsAffineOpen U →
      Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) ∧
      Module.Flat Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) ∧
      ∀ p : PrimeSpectrum Γ(U.toScheme, ⊤), Module.rankAtStalk Γ(M.restrict U.ι, ⊤) p = 1) :
    Line.Bundles.LineBundle X where
  sheaf := M
  locallyTrivial x := by
    have hx : x ∈ ⨆ U : X.affineOpens, U.1 := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have : IsAffine U.1.toScheme := U.2
    obtain ⟨hfinite, hflat, hrank⟩ := h U.1 U.2
    obtain ⟨V, hxV, ⟨frame⟩⟩ := Affine.RankOneLocalFrames.affineRankOne_localFrames (M.restrict U.1.ι) hrank ⟨x, hxU⟩
    exact ⟨U.1.ι ''ᵁ V, U.1.mem_ι_image_iff.mpr hxV, ⟨RestrictionFrameImage.restrictionFrameImage M U.1 V frame⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.OfAffineRankOne
