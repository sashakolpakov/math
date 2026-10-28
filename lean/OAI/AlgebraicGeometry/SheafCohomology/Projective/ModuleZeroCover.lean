import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleEpiCover

/-! # Module Zero Cover -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleZeroCover

noncomputable section

/-! Vanishing of an actual module sheaf can be checked on an open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem module_isZero_of_restrict_cover {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (M : X.Modules)
    (hM : ∀ i, IsZero ((Scheme.Modules.restrictFunctor (U i).ι).obj M)) : IsZero M := by
  have : Epi (0 : M ⟶ M) :=
    ModuleEpiCover.Scheme.Modules.epi_of_restrictFunctor_map_epi_of_iSup_eq_top U hU 0 (fun i => by
      exact (hM i).epi _)
  exact IsZero.of_epi_zero M M

theorem module_isZero_of_pullback_cover {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (M : X.Modules)
    (hM : ∀ i, IsZero ((Scheme.Modules.pullback (U i).ι).obj M)) : IsZero M := by
  apply module_isZero_of_restrict_cover U hU M
  intro i
  exact ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app M).isZero_iff.mpr (hM i)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleZeroCover
