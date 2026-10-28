import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCohomology
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Compact Support Cochain Meaning -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCochainMeaning

noncomputable section

/-!
# The concrete support condition on compact-support cochains

The filtered colimit defining compact-support cochains embeds in the actual
ordinary singular cochains. Its degreewise image consists exactly of those
cochains whose restriction to the complement of some compact subset is zero.
This is a theorem about cochains; no injectivity of compact-support cohomology
in ordinary cohomology is asserted.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {R : Type} [Ring R]

/-- The actual compact-support diagram evaluated in one cochain degree. -/
abbrev compactSupportDegreeCocone (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Cocone (CompactSupportCohomology.compactSupportCochainDiagram M X ⋙
      HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n) :=
  (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapCocone
    (colimit.cocone (CompactSupportCohomology.compactSupportCochainDiagram M X))

/-- Evaluation in a cochain degree preserves this genuine colimit. -/
def compactSupportDegreeIsColimit (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    IsColimit (compactSupportDegreeCocone M X n) :=
  isColimitOfPreserves (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n)
    (colimit.isColimit (CompactSupportCohomology.compactSupportCochainDiagram M X))

/-- Every compact-support cochain is already represented at one compact support. -/
theorem compactSupportedCochains_exists_stage (M : ModuleCat.{0} R) (X : TopCat.{0})
    (n : ℕ) (c : (CompactSupportCohomology.compactSupportedCochains M X).X n) :
    ∃ (K : Compacts X) (a : (CompactSupportCohomology.compactSupportCochainStage M X K).X n),
      (CompactSupportCohomology.compactSupportCochainι M X K).f n a = c :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (ModuleCat.{0} R))
      (compactSupportDegreeIsColimit M X n)) c

@[simp]
theorem compactSupportCochainι_forget_apply (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) (n : ℕ) (a : (CompactSupportCohomology.compactSupportCochainStage M X K).X n) :
    (CompactSupportCohomology.compactSupportedCochainForget M X).f n ((CompactSupportCohomology.compactSupportCochainι M X K).f n a) =
      (CompactSupportCohomology.compactSupportCochainStageInclusion M X K).f n a :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (CompactSupportCohomology.compactSupportCochainι_forget M X K) n) a

/-- Forgetting compact support is injective on actual cochains in every degree. -/
theorem compactSupportedCochainForget_injective (M : ModuleCat.{0} R) (X : TopCat.{0})
    (n : ℕ) : Function.Injective ((CompactSupportCohomology.compactSupportedCochainForget M X).f n) := by
  intro x y hxy
  obtain ⟨K, a, b, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget (ModuleCat.{0} R))
      (compactSupportDegreeIsColimit M X n)) x y
  apply congrArg ((CompactSupportCohomology.compactSupportCochainι M X K).f n)
  apply (ModuleCat.mono_iff_injective ((CompactSupportCohomology.compactSupportCochainStageInclusion M X K).f n)).mp
    (inferInstance : Mono ((CompactSupportCohomology.compactSupportCochainStageInclusion M X K).f n))
  change (CompactSupportCohomology.compactSupportedCochainForget M X).f n ((CompactSupportCohomology.compactSupportCochainι M X K).f n a) =
    (CompactSupportCohomology.compactSupportedCochainForget M X).f n ((CompactSupportCohomology.compactSupportCochainι M X K).f n b) at hxy
  exact (compactSupportCochainι_forget_apply M X K n a).symm.trans
    (hxy.trans (compactSupportCochainι_forget_apply M X K n b))

/-- Compact-support cochains form an actual subcomplex of singular cochains. -/
instance compactSupportedCochainForget_mono (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    Mono (CompactSupportCohomology.compactSupportedCochainForget M X) :=
  HomologicalComplex.mono_of_mono_f _ (fun n =>
    (ModuleCat.mono_iff_injective _).mpr (compactSupportedCochainForget_injective M X n))

/-- The image consists exactly of ordinary cochains vanishing on the complement
of a compact subset, with no further support assumption. -/
theorem mem_compactSupportedCochainForget_range_iff (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (c : (Cohomology.Singular.Basic.singularCochains M X).X n) :
    c ∈ LinearMap.range ((CompactSupportCohomology.compactSupportedCochainForget M X).f n).hom ↔
      ∃ K : Compacts X, (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X (K : Set X)ᶜ).f n c = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨K, b, hb⟩ := compactSupportedCochains_exists_stage M X n a
    refine ⟨K, ?_⟩
    rw [← hb, compactSupportCochainι_forget_apply]
    have hmem : (CompactSupportCohomology.compactSupportCochainStageInclusion M X K).f n b ∈
        LinearMap.range ((CompactSupportCohomology.compactSupportCochainStageInclusion M X K).f n).hom := ⟨b, rfl⟩
    rw [CompactSupportCohomology.compactSupportCochainStage_range] at hmem
    exact hmem
  · rintro ⟨K, hc⟩
    have hmem : c ∈ LinearMap.range ((CompactSupportCohomology.compactSupportCochainStageInclusion M X K).f n).hom := by
      rw [CompactSupportCohomology.compactSupportCochainStage_range]
      exact hc
    obtain ⟨a, ha⟩ := hmem
    refine ⟨(CompactSupportCohomology.compactSupportCochainι M X K).f n a, ?_⟩
    simpa only [compactSupportCochainι_forget_apply] using ha

/-- Each degree is canonically linearly equivalent to its genuine submodule
of ordinary singular cochains with the compact-support condition above. -/
def compactSupportedCochainRangeEquiv (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    (CompactSupportCohomology.compactSupportedCochains M X).X n ≃ₗ[R]
      LinearMap.range ((CompactSupportCohomology.compactSupportedCochainForget M X).f n).hom :=
  LinearEquiv.ofInjective ((CompactSupportCohomology.compactSupportedCochainForget M X).f n).hom
    (compactSupportedCochainForget_injective M X n)

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCochainMeaning
