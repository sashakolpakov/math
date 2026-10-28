import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Complex.Basic

/-! # Period Transversality -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.PeriodTransversality.Abelian

noncomputable section

/-!
The transverse period chart is open for continuously varying period
frames. The proof uses openness of invertible continuous linear maps,
applied to the frame together with a fixed complementary subspace.
-/

open scoped _root_.Topology

variable {S E F : Type*} [TopologicalSpace S]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem isCompl_range_of_coprod_equiv (f : E →L[ℂ] F) (W : Submodule ℂ F)
    (e : (E × W) ≃L[ℂ] F) (he : e.toContinuousLinearMap = f.coprod W.subtypeL) :
    IsCompl f.toLinearMap.range W := by
  have h := (Submodule.orderIsoMapComap e.toLinearEquiv).isCompl
    (LinearMap.isCompl_range_inl_inr (R := ℂ) (M := E) (M₂ := W))
  change IsCompl ((LinearMap.inl ℂ E W).range.map e.toLinearEquiv.toLinearMap)
    ((LinearMap.inr ℂ E W).range.map e.toLinearEquiv.toLinearMap) at h
  have he' : e.toLinearEquiv.toLinearMap = f.toLinearMap.coprod W.subtype :=
    congrArg ContinuousLinearMap.toLinearMap he
  rw [← LinearMap.range_comp, ← LinearMap.range_comp, he', LinearMap.coprod_inl,
    LinearMap.coprod_inr, Submodule.range_subtype] at h
  exact h

/-- Transversality to a fixed complement persists in a neighborhood. -/
theorem eventually_isCompl_range (f : S → E →L[ℂ] F) (s₀ : S)
    (hf : ContinuousAt f s₀) (W : Submodule ℂ F)
    (hi : Function.Injective (f s₀)) (hW : IsCompl (f s₀).toLinearMap.range W) :
    ∀ᶠ s in 𝓝 s₀, IsCompl (f s).toLinearMap.range W := by
  let e₁ := LinearEquiv.ofInjective (f s₀).toLinearMap hi
  let e₂ := ((f s₀).toLinearMap.range).prodEquivOfIsCompl W hW
  let e₀ := ((e₁.prodCongr (LinearEquiv.refl ℂ W)).trans e₂).toContinuousLinearEquiv
  have he₀ : e₀.toContinuousLinearMap = (f s₀).coprod W.subtypeL := by
    apply ContinuousLinearMap.ext
    rintro ⟨x, w⟩
    change (f s₀) x + (w : F) = (f s₀) x + (w : F)
    rfl
  have hc : ContinuousAt (fun s => (f s).coprod W.subtypeL) s₀ :=
    hf.continuousLinearMapCoprod continuousAt_const
  let : CompleteSpace (E × W) := FiniteDimensional.complete ℂ _
  have hn : Set.range (fun e : (E × W) ≃L[ℂ] F => e.toContinuousLinearMap) ∈
      𝓝 ((f s₀).coprod W.subtypeL) := by
    rw [← he₀]
    exact e₀.nhds
  filter_upwards [hc.preimage_mem_nhds hn] with s hs
  obtain ⟨e, he⟩ := hs
  exact isCompl_range_of_coprod_equiv (f s) W e he

end

end OAI.ArithmeticGeometry.Descent.CMVariety.PeriodTransversality.Abelian
