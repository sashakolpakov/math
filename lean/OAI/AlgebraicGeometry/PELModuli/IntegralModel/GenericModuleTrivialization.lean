import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericFreeSections
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ModuleBasisIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictFreeSections
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictFiniteType

/-! # Generic Module Trivialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericModuleTrivialization

noncomputable section

/-! A coherent module on an integral locally noetherian scheme is
actually isomorphic to a finite free structure module on a nonempty
affine open inside any prescribed nonempty affine open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem exists_generic_module_trivialization
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) [Nonempty U.1] :
    ∃ V : X.Opens, V ≤ U.1 ∧ Nonempty V ∧ IsAffineOpen V ∧
      ∃ n : ℕ, Nonempty ((∐ fun _ : Fin n => SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V.toScheme) ≅ M.restrict V.ι) := by
  obtain ⟨V, hVU, hV, hVa, hfree⟩ := GenericFreeSections.exists_generic_free_sections M U
  let := hV
  let : IsAffine V.toScheme := hVa
  let := hfree
  let : Module.Free Γ(V.toScheme, ⊤) Γ(M.restrict V.ι, ⊤) :=
    RestrictFreeSections.restrict_globalSections_free M V
  let : (M.restrict V.ι).IsFiniteType := RestrictFiniteType.module_restrict_finiteType M V
  let : Module.Finite Γ(V.toScheme, ⊤) Γ(M.restrict V.ι, ⊤) :=
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.globalSections_module_finite_of_isFiniteType_of_isAffine (M.restrict V.ι)
  exact ⟨V, hVU, hV, hVa, _, ⟨Affine.ModuleBasisIso.affineModuleIsoOfBasis (M.restrict V.ι) _
    (Module.finBasis Γ(V.toScheme, ⊤) Γ(M.restrict V.ι, ⊤))⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericModuleTrivialization
