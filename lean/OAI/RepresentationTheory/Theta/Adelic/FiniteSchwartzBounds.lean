import OAI.RepresentationTheory.Theta.Adelic.CompactSupport
import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest
import OAI.RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles

/-! # Finite Schwartz Bounds -/

namespace OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartzBounds

noncomputable section

/-! Every actual finite Schwartz tensor has bounded values and a single
arithmetic denominator, so its rational support lies in a discrete
Minkowski lattice. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem finiteSchwartz_uniform_bound (f : FiniteSchwartz.finiteSchwartz F N) :
    ∃ C : ℝ, ∀ a, ‖Evaluation.finiteSchwartzFunction F N f a‖ ≤ C :=
  (CompactSupport.AdelicSchwartz.finiteSchwartzFunction_mem F N f).2.exists_bound_of_continuous
    (CompactSupport.AdelicSchwartz.finiteSchwartzFunction_mem F N f).1.continuous

theorem finiteSchwartz_denominator (f : FiniteSchwartz.finiteSchwartz F N) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ a : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F,
      Evaluation.finiteSchwartzFunction F N f a ≠ 0 →
      ∀ i, algebraMap (𝓞 F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r * a i ∈ Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F := by
  have hc := (CompactSupport.AdelicSchwartz.finiteSchwartzFunction_mem F N f).2
  obtain ⟨r, hr, hb⟩ := Weil.AdelicSplitting.IntegralAdeles.Construction.compact_subset_finiteIntegralBox F
    (tsupport (Evaluation.finiteSchwartzFunction F N f)) hc
  exact ⟨r, hr, fun a ha => hb (subset_tsupport _ ha)⟩

theorem finiteSchwartz_support_lattice (f : FiniteSchwartz.finiteSchwartz F N) :
    ∃ r : F, r ≠ 0 ∧ ∀ q : Weil.Local.FunctionsMetaplectic.Construction.Position F N,
      Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q) ≠ 0 →
        Weil.AdelicSplitting.ThetaTest.Construction.mixedRationalPosition F N q ∈ Weil.AdelicSplitting.ThetaTest.Construction.mixedPositionLattice F N r := by
  obtain ⟨r, hr, hb⟩ := finiteSchwartz_denominator F N f
  refine ⟨algebraMap (𝓞 F) F r,
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr, ?_⟩
  intro q hq
  apply Weil.AdelicSplitting.ThetaTest.Construction.rational_mem_mixedPositionLattice F N
  intro i
  have hi := hb (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q) hq i
  simpa only [Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition, map_mul, IsScalarTower.algebraMap_apply] using! hi

end

end OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartzBounds
