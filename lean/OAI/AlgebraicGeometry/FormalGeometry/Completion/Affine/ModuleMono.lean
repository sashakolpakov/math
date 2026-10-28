import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsMono

/-! # Module Mono -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ModuleMono

noncomputable section

/-! Global sections detect monomorphisms between quasicoherent modules on an affine scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

namespace Construction

universe u

theorem affineModuleMap_mono_of_globalSections_injective
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    (ha : Function.Injective (a.app ⊤)) : Mono a := by
  have hk := SheafCohomology.Projective.GlobalSectionsMono.globalSections_injective_of_mono (kernel.ι a)
  have hsub : Subsingleton Γ(kernel a, ⊤) := ⟨by
    intro x y
    apply hk
    apply ha
    have h := congrArg (fun f : kernel a ⟶ N => f.app ⊤) (kernel.condition a)
    have hx := ConcreteCategory.congr_hom h x
    have hy := ConcreteCategory.congr_hom h y
    exact hx.trans hy.symm⟩
  have : (kernel a).IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel a
  have hzero : IsIso ((0 : End (kernel a)).val.app (op ⊤)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fun _ _ _ => hsub.elim _ _, fun y => ⟨0, hsub.elim _ _⟩⟩
  have : IsIso (0 : End (kernel a)) :=
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top _ hzero
  apply Preadditive.mono_of_isZero_kernel a
  exact IsZero.of_epi_eq_zero (0 : End (kernel a)) rfl

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ModuleMono
