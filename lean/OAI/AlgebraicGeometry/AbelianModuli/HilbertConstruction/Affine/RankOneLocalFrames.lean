import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PrincipalRankOneSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.RankOneLocalBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleFrameFromSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictedSectionBases

/-! # Rank One Local Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RankOneLocalFrames

noncomputable section

/-! A quasicoherent sheaf on an affine scheme with finite flat global sections of constant rank one has actual local frames. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(X, ⊤) Γ(M, ⊤)] [Module.Flat Γ(X, ⊤) Γ(M, ⊤)]

theorem affineRankOne_localFrames
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤), Module.rankAtStalk Γ(M, ⊤) p = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty
      ((Scheme.Modules.pullback U.ι).obj M ≅ Line.Bundles.structureModule U.toScheme) := by
  let hX := isAffineOpen_top X
  let p := hX.primeIdealOf ⟨x, by trivial⟩
  obtain ⟨r, hr, ⟨e⟩⟩ := HilbertConstruction.Finite.RankOneLocalBasis.finiteFlatRankOne_localBasis hrank p
  let U := X.basicOpen r
  have hU : IsAffineOpen U := hX.basicOpen r
  have hxU : x ∈ U := by
    have hp : p ∈ hX.fromSpec ⁻¹ᵁ X.basicOpen r := by
      rw [hX.fromSpec_preimage_basicOpen r]
      exact hr
    change hX.fromSpec p ∈ U at hp
    simpa only [p, hX.fromSpec_primeIdealOf] using hp
  have : IsAffine U.toScheme := hU
  refine ⟨U, hxU, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫
    ModuleFrameFromSections.affineModuleFrameFromSections (M.restrict U.ι)
      (Open.RestrictedSectionBases.moduleRestrictTopBasisEquiv M U (PrincipalRankOneSections.affinePrincipalRankOneSections M r e))

def affineRankOneLineBundle
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤), Module.rankAtStalk Γ(M, ⊤) p = 1) : Line.Bundles.LineBundle X :=
  ⟨M, affineRankOne_localFrames M hrank⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RankOneLocalFrames
