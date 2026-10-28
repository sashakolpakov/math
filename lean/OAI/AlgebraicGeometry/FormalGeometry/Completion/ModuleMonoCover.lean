import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleRestrictLimits

/-! # Module Mono Cover -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ModuleMonoCover

noncomputable section

/-! Actual module monomorphisms can be checked on an open cover. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

theorem moduleMap_mono_of_locally_restrict {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N)
    (ha : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.restrictFunctor U.ι).map a)) : Mono a := by
  have hzero : IsIso (0 : End (kernel a)) := by
    apply AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
    intro x
    obtain ⟨U, hx, hU⟩ := ha x
    have := hU
    let F := Scheme.Modules.restrictFunctor U.ι
    have : PreservesLimits F := SheafCohomology.Projective.ModuleRestrictLimits.Scheme.Modules.restrictFunctor_preservesLimits U.ι
    have hk : IsZero (F.obj (kernel a)) :=
      ((Preadditive.mono_iff_isZero_kernel (F.map a)).mp hU).of_iso (PreservesKernel.iso F a)
    have hi : IsIso (F.map (0 : End (kernel a))) := hk.isIso hk _
    exact ⟨U, hx, (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff U.ι _).mp hi⟩
  have := hzero
  exact Preadditive.mono_of_isZero_kernel a (IsZero.of_epi_eq_zero (0 : End (kernel a)) rfl)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ModuleMonoCover
