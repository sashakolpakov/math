import OAI.Analysis.Normed.Function.Holder.Banach.Norm
import OAI.Analysis.Normed.Function.Holder.Banach.Maps

/-! Isometric pullback of the actual Hölder Banach spaces. -/

noncomputable section
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {X Y F : Type*} [MetricSpace X] [MetricSpace Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}

def holderIsometricPullbackValue (hα : 0 ≤ α) (g : X → Y) (hg : Isometry g)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap Y F α) : OAI.Analysis.Normed.Function.Holder.HolderMap X F α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα ((OAI.Analysis.Normed.Function.Holder.HolderMap.value f).compContinuous ⟨g, hg.continuous⟩)
    (fun x y => by
      change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value f (g x) - OAI.Analysis.Normed.Function.Holder.HolderMap.value f (g y)‖ ≤ ‖f‖ * (dist x y) ^ α
      rw [← hg.dist_eq x y]
      exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (g x) (g y))

def holderIsometricPullback (hα : 0 ≤ α) (g : X → Y) (hg : Isometry g) :
    OAI.Analysis.Normed.Function.Holder.HolderMap Y F α →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X F α :=
  LinearMap.mkContinuous {
    toFun := holderIsometricPullbackValue hα g hg
    map_add' := by
      intro f f'
      apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
      ext x
      rfl
    map_smul' := by
      intro c f
      apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
      ext x
      rfl } 1 (by
    intro f
    simp only [one_mul]
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (norm_nonneg f)
    · intro x
      exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f (g x)
    · intro x y
      change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value f (g x) - OAI.Analysis.Normed.Function.Holder.HolderMap.value f (g y)‖ ≤ _
      simpa only [hg.dist_eq] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (g x) (g y))

@[simp] theorem holderIsometricPullback_apply (hα : 0 ≤ α) (g : X → Y) (hg : Isometry g)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap Y F α) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderIsometricPullback hα g hg f) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value f (g x) := rfl

theorem norm_holderIsometricPullback_le (hα : 0 ≤ α) (g : X → Y) (hg : Isometry g)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap Y F α) : ‖holderIsometricPullback hα g hg f‖ ≤ ‖f‖ := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (norm_nonneg f)
  · intro x
    exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f (g x)
  · intro x y
    change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value f (g x) - OAI.Analysis.Normed.Function.Holder.HolderMap.value f (g y)‖ ≤ _
    simpa only [hg.dist_eq] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (g x) (g y)

end OAI.Analysis.PDE.Schauder
