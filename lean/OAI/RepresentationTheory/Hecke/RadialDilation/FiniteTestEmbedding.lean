import OAI.RepresentationTheory.Hecke.RadialDilation.Mem
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Finite Test Embedding -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteTestEmbedding.Realization

noncomputable section

/-! Actual finite-adelic test functions from a split-place coordinate chart. -/

open scoped Classical _root_.Topology
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

local instance c410FiniteTestEmbedding_localInst1 (v : IsDedekindDomain.HeightOneSpectrum ℤ) : T2Space (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding.t2Space

local instance c410FiniteTestEmbedding_localInst2 : T2Space Theta.PoissonAutomorphyNormalizationData.AQf := by
  exact T2Space.of_injective_continuous
    (f := fun a : Theta.PoissonAutomorphyNormalizationData.AQf => fun v : IsDedekindDomain.HeightOneSpectrum ℤ => a v)
    DFunLike.coe_injective RestrictedProduct.continuous_coe

variable (q : ℕ) [Fact q.Prime]

theorem radialBall_regular (j : ℤ) :
    IsLocallyConstant (Mem.Realization.radialBall q j) ∧ HasCompactSupport (Mem.Realization.radialBall q j) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  let K := Metric.closedBall (0 : Mem.Realization.Position q) ((q : ℝ) ^ (-j))
  have hK : IsClopen K :=
    IsUltrametricDist.isClopen_closedBall _ (zpow_pos hq (-j)).ne'
  rw [Mem.Realization.radialBall_closedBall]
  refine ⟨(LocallyConstant.charFn ℂ hK).isLocallyConstant, ?_⟩
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Mem.Realization.Position q) ((q : ℝ) ^ (-j)))
  intro x hx
  exact Set.indicator_of_notMem hx _

theorem radial_regular (b : Cm.radialInput q) : IsLocallyConstant b.val ∧ HasCompactSupport b.val := by
  obtain ⟨b, hb⟩ := b
  induction hb using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨j, rfl⟩ := hf
      exact radialBall_regular q j
  | zero => exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  | smul c f _ hf => exact ⟨hf.1.comp (fun z : ℂ => c * z), hf.2.smul_left⟩

theorem product_test_compactSupport
    {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [T2Space W]
    (e : W ≃ₜ X × Y) (f : X → ℂ) (g : Y → ℂ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun w => f (e w).1 * g (e w).2) := by
  apply HasCompactSupport.intro ((hf.prod hg).image e.symm.continuous)
  intro w hw
  by_contra hne
  apply hw
  refine ⟨e w, ⟨?_, ?_⟩, e.symm_apply_apply w⟩
  · exact subset_closure (mul_ne_zero_iff.mp hne).1
  · exact subset_closure (mul_ne_zero_iff.mp hne).2

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

/-- The auxiliary factor is fixed while the actual radial input varies.
The chart is a homeomorphism of the finite-adelic position space. -/
def finiteRadialEmbedding
    (e : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ Mem.Realization.Position q × X)
    (φ : X → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    Cm.radialInput q →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι where
  toFun b := ⟨fun x => b.val (e x).1 * φ (e x).2,
    Submodule.subset_span ⟨
      ((radial_regular q b).1.comp_continuous (continuous_fst.comp e.continuous)).mul
        (hφ.comp_continuous (continuous_snd.comp e.continuous)),
      product_test_compactSupport e b.val φ (radial_regular q b).2 hcφ⟩⟩
  map_add' b c := by apply Subtype.ext; funext x; exact add_mul _ _ _
  map_smul' c b := by apply Subtype.ext; funext x; exact mul_assoc _ _ _

theorem finiteRadialEmbedding_injective
    (e : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ Mem.Realization.Position q × X)
    (φ : X → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (hnφ : φ ≠ 0) : Function.Injective (finiteRadialEmbedding q e φ hφ hcφ) := by
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hnφ
  intro b c h
  apply Subtype.ext
  funext x
  have he := congrArg (fun f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι => f.val (e.symm (x, y))) h
  change b.val (e (e.symm (x, y))).1 * φ (e (e.symm (x, y))).2 =
    c.val (e (e.symm (x, y))).1 * φ (e (e.symm (x, y))).2 at he
  rw [e.apply_symm_apply] at he
  exact mul_right_cancel₀ hy he

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteTestEmbedding.Realization
