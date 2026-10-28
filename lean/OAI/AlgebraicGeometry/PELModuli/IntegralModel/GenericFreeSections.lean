import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalizedModuleFreeTransfer
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericFlatness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Generic Free Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericFreeSections

noncomputable section

/-! Generic freeness for the actual sections of a coherent module on an
integral locally noetherian scheme. The resulting open lies in any given
nonempty affine open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem exists_generic_free_sections
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) [Nonempty U.1] :
    ∃ V : X.Opens, V ≤ U.1 ∧ Nonempty V ∧ IsAffineOpen V ∧
      Module.Free Γ(X, V) Γ(M, V) := by
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen M U
  let : Module.FinitePresentation Γ(X, U.1) Γ(M, U.1) :=
    Module.finitePresentation_of_finite Γ(X, U.1) Γ(M, U.1)
  obtain ⟨r, hr, hfree⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.GenericFlatness.Construction.exists_nonzero_free_localization
    Γ(X, U.1) Γ(M, U.1)
  have hV : Nonempty (X.basicOpen r) := by
    apply Set.nonempty_coe_sort.mpr
    exact (Opens.ne_bot_iff_nonempty _).mp (fun h => hr ((basicOpen_eq_bot_iff r).mp h))
  refine ⟨X.basicOpen r, X.basicOpen_le r, hV, U.2.basicOpen r, ?_⟩
  let : Module Γ(X, U.1) Γ(M, X.basicOpen r) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r))
  let : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    .of_algebraMap_smul fun _ _ => rfl
  let : IsLocalization.Away r Γ(X, X.basicOpen r) := U.2.isLocalization_basicOpen r
  let g : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen r) :=
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le r)).op
      map_add' := (M.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.map_add
      map_smul' := fun a x => M.map_smul (homOfLE (X.basicOpen_le r)) a x }
  let : IsLocalizedModule.Away r g :=
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isLocalizedModuleAway_basicOpen_of_isQuasicoherent_of_isAffineOpen M U r
  let := hfree
  exact LocalizedModuleFreeTransfer.free_of_isLocalizedModule_of_free_canonical (Submonoid.powers r)
    Γ(X, X.basicOpen r) g

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericFreeSections
