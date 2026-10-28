import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.GenericFreeSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleBasisIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionSectionFreeness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.RestrictionFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-! # Generic Module Trivialization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenericModuleTrivialization

noncomputable section

/-! A coherent module on an integral locally noetherian scheme is actually finite free on a nonempty affine open. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem exists_generic_module_trivialization
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) [Nonempty U.1] :
    ∃ V : X.Opens, V ≤ U.1 ∧ Nonempty V ∧ IsAffineOpen V ∧
      ∃ n : ℕ, Nonempty ((∐ fun _ : ULift.{u} (Fin n) => Line.Bundles.structureModule V.toScheme) ≅
        M.restrict V.ι) := by
  obtain ⟨V, hVU, hV, hVa, hfree⟩ := Coherent.GenericFreeSections.exists_generic_free_sections M U
  let := hV
  have : Nonempty V.toScheme := hV
  have : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨Classical.choice hV, trivial⟩⟩
  have : Nontrivial Γ(V.toScheme, ⊤) := Scheme.component_nontrivial V.toScheme ⊤
  have : StrongRankCondition Γ(V.toScheme, ⊤) := inferInstance
  let : IsAffine V.toScheme := hVa
  let := hfree
  let : Module.Free Γ(V.toScheme, ⊤) Γ(M.restrict V.ι, ⊤) :=
    RestrictionSectionFreeness.restrict_globalSections_free M V
  let : (M.restrict V.ι).IsFiniteType := Quasicoherent.RestrictionFiniteType.quasicoherent_openRestrict_finiteType V.ι M
  let : Module.Finite Γ(V.toScheme, ⊤) Γ(M.restrict V.ι, ⊤) :=
    Affine.QuasicoherentFiniteTypeSections.affine_quasicoherent_finiteType_sections_finite (M.restrict V.ι)
  exact ⟨V, hVU, hV, hVa, _, ⟨Affine.ModuleBasisIsomorphism.affineModuleIsoOfBasis (M.restrict V.ι) _
    ((Module.finBasis Γ(V.toScheme, ⊤) Γ(M.restrict V.ι, ⊤)).reindex Equiv.ulift.symm)⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenericModuleTrivialization
