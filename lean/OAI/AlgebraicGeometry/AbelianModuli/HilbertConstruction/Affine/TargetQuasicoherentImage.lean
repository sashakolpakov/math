import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImageQuasicoherentLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationRestrictScalars
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Target Quasicoherent Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TargetQuasicoherentImage

noncomputable section

/-! Quasi-compact separated direct images to affine spectra preserve quasicoherence by actual section localization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem quasicoherent_directImage_over_spectrum
    {R : CommRingCat.{u}} {X : Scheme.{u}} [CompactSpace X]
    [X.IsSeparated]
    (f : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward f).obj M
  apply (isQuasicoherent_iff_isIso_fromTildeΓ N).mpr
  apply (isIso_fromTildeΓ_iff_isLocalizing N).mpr
  intro r
  let φ := (Scheme.ΓSpecIso R).inv.hom
  let s : Γ(Spec R, ⊤) := φ r
  have := ImageQuasicoherentLocalization.quasicoherent_directImage_sections_localize f M s
  have h := LocalizationRestrictScalars.coefficientSection_localization_restrictScalars φ (RingHom.id Γ(Spec R, ⊤))
    N ((Spec R).basicOpen s) r
  have hs : (Spec R).basicOpen s = PrimeSpectrum.basicOpen r := basicOpen_eq_of_affine r
  rw [hs] at h
  exact h

theorem quasiCompact_separated_directImage_over_spectrum
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) [QuasiCompact f] [IsSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  exact quasicoherent_directImage_over_spectrum f M

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TargetQuasicoherentImage
