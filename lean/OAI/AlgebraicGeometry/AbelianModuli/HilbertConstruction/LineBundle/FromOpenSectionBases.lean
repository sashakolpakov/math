import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleFrameFromSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictedSectionBases

/-! # From Open Section Bases -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenSectionBases

noncomputable section

/-! Actual bases of open-section modules on a quasicoherent sheaf construct local frames and hence a line bundle. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

def lineBundleFromOpenSectionBases (M : X.Modules) [M.IsQuasicoherent]
    (e : ∀ U : X.Opens, Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) : Line.Bundles.LineBundle X where
  sheaf := M
  locallyTrivial x := by
    have hx : x ∈ ⨆ U : X.affineOpens, U.1 := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have : IsAffine U.1.toScheme := U.2
    refine ⟨U.1, hxU, ⟨?_⟩⟩
    exact (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).symm.app M ≪≫
      Affine.ModuleFrameFromSections.affineModuleFrameFromSections (M.restrict U.1.ι) (Open.RestrictedSectionBases.moduleRestrictTopBasisEquiv M U.1 (e U.1))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenSectionBases
