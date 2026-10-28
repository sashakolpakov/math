import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionAdjunction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Spectrum Line Bundle Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.SpectrumLineBundleFrames

noncomputable section

/-! Every line bundle on the spectrum of a local ring has a global
frame: an open trivialization containing the closed point covers the
whole spectrum. The resulting isomorphism is between actual sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem localSpectrum_lineBundle_trivial {R : Type u} [CommRing R] [IsLocalRing R]
    (L : Line.Bundles.LineBundle (Spec (.of R))) : Nonempty (L.sheaf ≅ Line.Bundles.structureModule (Spec (.of R))) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := L.locallyTrivial (IsLocalRing.closedPoint R)
  have htop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hU
  subst U
  let f := (⊤ : (Spec (.of R)).Opens).ι
  have : IsIso f := isIso_of_isOpenImmersion_of_opensRange_eq_top f (by simp [f])
  let F := Scheme.Modules.pullback f
  have : F.IsEquivalence := Affine.SectionAdjunction.AffineSectionAdjunction.pullback_equivalence (asIso f)
  exact ⟨F.preimageIso (e ≪≫ (Line.Bundles.structureModulePullbackIso f).symm)⟩

def localSpectrumLineBundleIso {R : Type u} [CommRing R] [IsLocalRing R]
    (L : Line.Bundles.LineBundle (Spec (.of R))) : L.sheaf ≅ Line.Bundles.structureModule (Spec (.of R)) :=
  Classical.choice (localSpectrum_lineBundle_trivial L)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.SpectrumLineBundleFrames
