import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImageLineBundleLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationRestrictScalars
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Target Line Bundle Quasicoherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TargetLineBundleQuasicoherence

noncomputable section

/-! Line-bundle direct images to affine spectra are quasicoherent, proved from actual section localization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem lineBundle_directImage_quasicoherent_over_spectrum
    {R : CommRingCat.{u}} {X : Scheme.{u}} [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec R) (L : Line.Bundles.LineBundle X) :
    ((Scheme.Modules.pushforward f).obj L.sheaf).IsQuasicoherent := by
  let M := (Scheme.Modules.pushforward f).obj L.sheaf
  apply (isQuasicoherent_iff_isIso_fromTildeΓ M).mpr
  apply (isIso_fromTildeΓ_iff_isLocalizing M).mpr
  intro r
  let φ := (Scheme.ΓSpecIso R).inv.hom
  let s : Γ(Spec R, ⊤) := φ r
  have := ImageLineBundleLocalization.lineBundle_directImage_sections_localize f L s
  have h := LocalizationRestrictScalars.coefficientSection_localization_restrictScalars φ (RingHom.id Γ(Spec R, ⊤))
    M ((Spec R).basicOpen s) r
  have hs : (Spec R).basicOpen s = PrimeSpectrum.basicOpen r := basicOpen_eq_of_affine r
  rw [hs] at h
  exact h

theorem proper_lineBundle_directImage_quasicoherent_over_spectrum
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) [IsProper f]
    (L : Line.Bundles.LineBundle X) : ((Scheme.Modules.pushforward f).obj L.sheaf).IsQuasicoherent := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  exact lineBundle_directImage_quasicoherent_over_spectrum f L

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TargetLineBundleQuasicoherence
