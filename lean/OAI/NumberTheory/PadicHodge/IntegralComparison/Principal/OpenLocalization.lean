import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization

/-! # Open Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenLocalization

noncomputable section

/-! The literal source-open restriction in the original principal
diagram clears denominators and has power-torsion kernel. The scalar is
the original section on the inverse image of the ambient affine open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem denominator_of_eq {Y : Scheme.{u}} (N : Y.Modules) [N.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U) (a : Γ(Y, U))
    (T : Y.Opens) (hTU : T ≤ U) (hT : T = Y.basicOpen a) (x : Γ(N, T)) :
    ∃ n : ℕ, ∃ y : Γ(N, U),
      N.presheaf.map (homOfLE hTU).op y = Y.presheaf.map (homOfLE hTU).op (a^n) • x := by
  subst T
  exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionExtension.affineOpen_quasicoherent_section_clear_denominator N ⟨U, hU⟩ a x

private theorem kernel_of_eq {Y : Scheme.{u}} (N : Y.Modules) [N.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U) (a : Γ(Y, U))
    (T : Y.Opens) (hTU : T ≤ U) (hT : T = Y.basicOpen a)
    (x : Γ(N, U)) (hx : N.presheaf.map (homOfLE hTU).op x = 0) :
    ∃ n : ℕ, a^n • x = 0 := by
  subst T
  exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionVanishing.affineOpen_quasicoherent_section_vanishing N ⟨U, hU⟩ a x hx

private theorem extension_smul {Y : Scheme.{u}} (N : Y.Modules) (V U : Y.Opens)
    (a : Γ(Y, U)) (x : Γ(PrincipalSource.OpenRestriction.extension V N, U)) :
    a • x = Y.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op a •
      (show Γ(N, V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) from x) := by
  change Γ(N, V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) at x
  change (V.ι.appIso (V.ι ⁻¹ᵁ U)).inv (V.ι.app U a) • x = _
  exact congrArg (fun b : Γ(Y, V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) => b • x)
    (ConcreteCategory.congr_hom (V.ι.app_appIso_inv U) a)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars
variable {Y Z : Scheme.{u}} (π : Y ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (N : Y.Modules)
  (z : Γ(Y, π ⁻¹ᵁ U))

abbrev targetSheaf := PrincipalSource.OpenRestriction.extension (Y.basicOpen z) N
abbrev source := ClosedScalars.modules π U hU N
abbrev target := ClosedScalars.modules π U hU (targetSheaf π U N z)

def map : source π U hU N ⟶ target π U hU N z :=
  ClosedScalars.moduleHom π U hU
    ((Scheme.Modules.restrictAdjunction (Y.basicOpen z).ι).unit.app N)

abbrev restricted (r : SectionPresheaf.Index U) : Γ(Y, ClosedScalars.pullbackOpen π U r) :=
  Y.presheaf.map (ClosedScalars.pullbackInclusion π U r).op z
abbrev localOpen (r : SectionPresheaf.Index U) := (Y.basicOpen z).ι ''ᵁ
  ((Y.basicOpen z).ι ⁻¹ᵁ ClosedScalars.pullbackOpen π U r)
abbrev localInclusion (r : SectionPresheaf.Index U) : localOpen π U z r ⟶ ClosedScalars.pullbackOpen π U r :=
  homOfLE ((Y.basicOpen z).ι.image_preimage_le (ClosedScalars.pullbackOpen π U r))
abbrev ambientInclusion (r : SectionPresheaf.Index U) : localOpen π U z r ⟶ π ⁻¹ᵁ U :=
  localInclusion π U z r ≫ ClosedScalars.pullbackInclusion π U r

theorem localOpen_eq (r : SectionPresheaf.Index U) : localOpen π U z r = Y.basicOpen (restricted π U z r) := by
  rw [localOpen, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    restricted, Scheme.basicOpen_res, inf_comm]

theorem map_app (r : SectionPresheaf.Index U) (x : (source π U hU N).obj (op r)) :
    (OpenLocalization.map π U hU N z).app (op r) x = N.presheaf.map (localInclusion π U z r).op x := rfl

theorem target_smul (r : SectionPresheaf.Index U) (a : Γ(Y, π ⁻¹ᵁ U))
    (x : (target π U hU N z).obj (op r)) :
    a • x = Y.presheaf.map (ambientInclusion π U z r).op a •
      (show Γ(N, localOpen π U z r) from x) := by
  change Γ(targetSheaf π U N z, ClosedScalars.pullbackOpen π U r) at x
  change ((Y.presheaf.map (ClosedScalars.pullbackInclusion π U r).op a) • x :
    Γ(targetSheaf π U N z, ClosedScalars.pullbackOpen π U r)) = _
  rw [extension_smul]
  rw [← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp]
  rfl

theorem scalar_power (r : SectionPresheaf.Index U) (n : ℕ) :
    Y.presheaf.map (localInclusion π U z r).op ((restricted π U z r)^n) =
      Y.presheaf.map (ambientInclusion π U z r).op (z^n) := by
  rw [restricted, ← map_pow, ← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp]
  rfl

variable [IsAffineHom π] [N.IsQuasicoherent]

theorem denominators (r : SectionPresheaf.Index U) (x : (target π U hU N z).obj (op r)) :
    ∃ n : ℕ, ∃ y : (source π U hU N).obj (op r),
      (OpenLocalization.map π U hU N z).app (op r) y = z^n • x := by
  obtain ⟨n, y, hy⟩ := denominator_of_eq N (ClosedScalars.pullbackOpen π U r)
    ((hU.basicOpen r.val).preimage π) (restricted π U z r) (localOpen π U z r)
    (localInclusion π U z r).le (localOpen_eq π U z r) x
  refine ⟨n, y, ?_⟩
  rw [map_app, target_smul]
  exact hy.trans (congrArg (fun a : Γ(Y, localOpen π U z r) => a •
    (show Γ(N, localOpen π U z r) from x)) (scalar_power π U z r n))

theorem kernel_power (r : SectionPresheaf.Index U) (x : (source π U hU N).obj (op r))
    (hx : (OpenLocalization.map π U hU N z).app (op r) x = 0) :
    ∃ n : ℕ, z^n • x = 0 := by
  obtain ⟨n, hn⟩ := kernel_of_eq N (ClosedScalars.pullbackOpen π U r)
    ((hU.basicOpen r.val).preimage π) (restricted π U z r) (localOpen π U z r)
    (localInclusion π U z r).le (localOpen_eq π U z r) x hx
  refine ⟨n, ?_⟩
  change Y.presheaf.map (ClosedScalars.pullbackInclusion π U r).op (z^n) •
    (show Γ(N, ClosedScalars.pullbackOpen π U r) from x) = 0
  rw [map_pow]
  exact hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenLocalization
