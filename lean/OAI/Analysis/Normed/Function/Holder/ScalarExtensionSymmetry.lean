import OAI.Analysis.Normed.Function.Holder.ScalarExtension

open Set
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

variable {X : Type*} [MetricSpace X] {K : Set X}

/-- The infimum extension respects every isometric symmetry of the input
set and data. This is used to preserve lattice periodicity before smoothing. -/
theorem holderInfExtension_isometry (f : K → ℝ) (H α : ℝ)
    (e : X ≃ᵢ X) (σ : K ≃ K) (hσ : ∀ y : K, (σ y : X) = e y)
    (hf : ∀ y : K, f (σ y) = f y) (x : X) :
    holderInfExtension f H α (e x) = holderInfExtension f H α x := by
  have ht (y : K) : f (σ y) + H * dist (e x) (σ y) ^ α = f y + H * dist x y ^ α := by
    rw [hf y, hσ y, e.dist_eq]
  change sInf (range (fun y : K ↦ f y + H * dist (e x) y ^ α)) =
    sInf (range (fun y : K ↦ f y + H * dist x y ^ α))
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy⟩
    have ht' := ht (σ.symm y)
    rw [σ.apply_symm_apply] at ht'
    exact ⟨σ.symm y, ht'.symm.trans hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨σ y, (ht y).trans hy⟩

theorem boundedHolderExtension_isometry (f : K → ℝ) (B H α : ℝ)
    (e : X ≃ᵢ X) (σ : K ≃ K) (hσ : ∀ y : K, (σ y : X) = e y)
    (hf : ∀ y : K, f (σ y) = f y) (x : X) :
    boundedHolderExtension f B H α (e x) = boundedHolderExtension f B H α x := by
  unfold boundedHolderExtension
  rw [holderInfExtension_isometry f H α e σ hσ hf x]

end OAI.Analysis.Normed.Function.Holder
