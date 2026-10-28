import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PresentationGenericFreeness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleFreenessTransfer
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Generic Free Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.GenericFreeSections

noncomputable section

/-! An actual coherent module has finite free sections on a nonempty affine open inside any prescribed nonempty affine open of an integral locally Noetherian scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

theorem exists_generic_free_sections
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) [Nonempty U.1] :
    ∃ V : X.Opens, V ≤ U.1 ∧ Nonempty V ∧ IsAffineOpen V ∧
      Module.Free Γ(X, V) Γ(M, V) := by
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
    Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite M U
  let : Module.FinitePresentation Γ(X, U.1) Γ(M, U.1) :=
    Module.finitePresentation_of_finite Γ(X, U.1) Γ(M, U.1)
  obtain ⟨r, hr, hfree⟩ := HilbertConstruction.Finite.PresentationGenericFreeness.exists_nonzero_free_localization
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
    AffineOpen.QuasicoherentLocalization.affineOpen_quasicoherent_sections_localize M U r
  let := hfree
  exact Localized.ModuleFreenessTransfer.free_of_isLocalizedModule_of_free_canonical (Submonoid.powers r)
    Γ(X, X.basicOpen r) g

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.GenericFreeSections
