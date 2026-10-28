import OAI.AlgebraicGeometry.Comparison.Betti.CochainZeroCriterion
import OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExactFunctor
import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt

/-! # Stalk Closed Lift Criterion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.StalkClosedLiftCriterion.Homology

noncomputable section

/-! A local closed-section lifting criterion for comparison at a
truncation boundary in actual stalk complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open _root_.TopCat.Presheaf

variable {X : TopCat.{0}}

theorem stalk_short_quasiIso_of_local_closed_lift
    {S T : ShortComplex (X.Presheaf (ModuleCat.{0} ℂ))} (f : S ⟶ T) (x : X)
    (hS : S.f = 0) (hT : T.f = 0) [Mono f.τ₂]
    (hs : ∀ (U : Opens X) (y : T.X₂.obj (op U)), T.g.app (op U) y = 0 →
      ∃ z : S.X₂.obj (op U), S.g.app (op U) z = 0 ∧ f.τ₂.app (op U) z = y) :
    ShortComplex.QuasiIso ((stalkFunctor (ModuleCat.{0} ℂ) x).mapShortComplex.map f) := by
  let F := stalkFunctor (ModuleCat.{0} ℂ) x
  apply CochainZeroCriterion.Homology.short_quasiIso_of_closed_lift
  · change F.map S.f = 0
    rw [hS, F.map_zero]
  · change F.map T.f = 0
    rw [hT, F.map_zero]
  · exact (ModuleCat.mono_iff_injective (F.map f.τ₂)).mp inferInstance
  · intro y hy
    change F.map T.g y = 0 at hy
    obtain ⟨U, hxU, s, rfl⟩ := T.X₂.exists_germ_eq y
    rw [stalkFunctor_map_germ_apply] at hy
    obtain ⟨V, hxV, i, hi⟩ :=
      (AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.germ_eq_zero_iff_locally_zero T.X₃ x U hxU (T.g.app (op U) s)).mp hy
    have hclosed : T.g.app (op V) (T.X₂.map i.op s) = 0 :=
      (ConcreteCategory.congr_hom (T.g.naturality i.op) s).trans hi
    obtain ⟨z, hz, he⟩ := hs V (T.X₂.map i.op s) hclosed
    refine ⟨S.X₂.germ V x hxV z, ?_, ?_⟩
    · change F.map S.g (S.X₂.germ V x hxV z) = 0
      rw [stalkFunctor_map_germ_apply, hz, map_zero]
      rfl
    · change F.map f.τ₂ (S.X₂.germ V x hxV z) = T.X₂.germ U x hxU s
      rw [stalkFunctor_map_germ_apply, he]
      exact T.X₂.germ_res_apply i x hxV s

theorem stalk_short_quasiIso_of_local_lift
    {S T : ShortComplex (X.Presheaf (ModuleCat.{0} ℂ))} (f : S ⟶ T) (x : X)
    (hS : S.f = 0) (hT : T.f = 0) [Mono f.τ₂] [Mono f.τ₃]
    (hs : ∀ (U : Opens X) (y : T.X₂.obj (op U)), T.g.app (op U) y = 0 →
      ∃ z : S.X₂.obj (op U), f.τ₂.app (op U) z = y) :
    ShortComplex.QuasiIso ((stalkFunctor (ModuleCat.{0} ℂ) x).mapShortComplex.map f) := by
  apply stalk_short_quasiIso_of_local_closed_lift f x hS hT
  intro U y hy
  obtain ⟨z, hz⟩ := hs U y hy
  refine ⟨z, ?_, hz⟩
  apply (ModuleCat.mono_iff_injective (f.τ₃.app (op U))).mp inferInstance
  have h := ConcreteCategory.congr_hom (congrArg (fun η => η.app (op U)) f.comm₂₃) z
  change T.g.app (op U) (f.τ₂.app (op U) z) = f.τ₃.app (op U) (S.g.app (op U) z) at h
  simpa only [hz, hy, map_zero] using h.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.StalkClosedLiftCriterion.Homology
