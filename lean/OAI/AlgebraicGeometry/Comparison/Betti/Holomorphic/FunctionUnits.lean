import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Restrictions

/-! # Function Units -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionUnits

noncomputable section

/-! Pointwise nonvanishing is exactly invertibility for actual holomorphic functions. -/

open _root_.TopologicalSpace
open scoped ContDiff _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Opens E}

def holomorphicFunctionInverse (f : FunctionPure.holomorphicFunctions U) (hf : ∀ x, f.val x ≠ 0) :
    FunctionPure.holomorphicFunctions U :=
  ⟨fun x => (f.val x)⁻¹, by
    have hs : ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U f.val) (U : Set E) := f.property
    apply (hs.inv (fun x hx => by
      rw [CoefficientMem.openCoefficientExtension_apply U _ ⟨x, hx⟩]
      exact hf ⟨x, hx⟩)).congr
    intro x hx
    simp only [Pi.inv_apply, CoefficientMem.openCoefficientExtension_apply U _ ⟨x, hx⟩]⟩

theorem isUnit_holomorphicFunction_iff (f : FunctionPure.holomorphicFunctions U) :
    IsUnit f ↔ ∀ x, f.val x ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ x hx
    have h := congrArg (fun g : FunctionPure.holomorphicFunctions U => g.val x) u.val_inv
    change u.val.val x * u.inv.val x = 1 at h
    rw [hx, zero_mul] at h
    exact zero_ne_one h
  · intro hf
    refine ⟨⟨f, holomorphicFunctionInverse f hf, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      funext x
      exact mul_inv_cancel₀ (hf x)
    · apply Subtype.ext
      funext x
      exact inv_mul_cancel₀ (hf x)

theorem exists_restrict_holomorphicFunction_isUnit (f : FunctionPure.holomorphicFunctions U)
    (x : U) (hx : f.val x ≠ 0) :
    ∃ (V : Opens E) (h : V ≤ U), (x : E) ∈ V ∧ IsUnit (Restrictions.holomorphicFunctionRestrict h f) := by
  have hs : ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U f.val) (U : Set E) := f.property
  have hc := (hs.contDiffAt (U.isOpen.mem_nhds x.property)).continuousAt
  have hx' : CoefficientMem.openCoefficientExtension U f.val x ≠ 0 := by
    rw [CoefficientMem.openCoefficientExtension_apply]
    exact hx
  have hn : ∀ᶠ y in 𝓝 (x : E), CoefficientMem.openCoefficientExtension U f.val y ≠ 0 :=
    hc.eventually_ne hx'
  obtain ⟨s, hs, ho, hxs⟩ := mem_nhds_iff.mp hn
  let V : Opens E := ⟨s ∩ U, ho.inter U.isOpen⟩
  refine ⟨V, fun _ h => h.2, ⟨hxs, x.property⟩, ?_⟩
  apply (isUnit_holomorphicFunction_iff _).mpr
  intro y
  have h := hs y.property.1
  change CoefficientMem.openCoefficientExtension U f.val y ≠ 0 at h
  rwa [CoefficientMem.openCoefficientExtension_apply U _ ⟨y, y.property.2⟩] at h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionUnits
