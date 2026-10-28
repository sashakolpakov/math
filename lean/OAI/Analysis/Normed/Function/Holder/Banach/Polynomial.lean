import OAI.Analysis.Normed.Function.Holder.Banach.Bilinear

open scoped BoundedContinuousFunction ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.HolderMap

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α : ℝ}

def constant (c : F) : HolderMap X F α := by
  refine ⟨(BoundedContinuousFunction.const X c, 0), ?_⟩
  intro q
  change (dist q.val.1 q.val.2) ^ α • (0 : F) = c - c
  simp

@[simp] theorem value_constant (c : F) (x : X) :
    HolderMap.value (HolderMap.constant (α := α) c) x = c := rfl

@[simp] theorem value_sum {ι : Type*} (s : Finset ι) (f : ι → HolderMap X F α) (x : X) :
    HolderMap.value (∑ i ∈ s, f i) x = ∑ i ∈ s, HolderMap.value (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, HolderMap.value_add, BoundedContinuousFunction.add_apply, ih,
      Finset.sum_insert hi]

section ComplexProducts

variable {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def listProduct (hα : 0 ≤ α) (l : List ι) (f : ι → HolderMap X ℂ α) : HolderMap X ℂ α :=
  l.foldr (fun i g ↦ HolderMap.bilinear hα (ContinuousLinearMap.mul ℝ ℂ) (f i) g) (HolderMap.constant 1)

@[simp] theorem value_listProduct (hα : 0 ≤ α) (l : List ι)
    (f : ι → HolderMap X ℂ α) (x : X) :
    HolderMap.value (HolderMap.listProduct hα l f) x = (l.map (fun i ↦ HolderMap.value (f i) x)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change HolderMap.value (f i) x * HolderMap.value (HolderMap.listProduct hα l f) x = _
    rw [ih]
    rfl

theorem contDiff_listProduct (hα : 0 ≤ α) (l : List ι) (n : ℕ∞ω)
    {f : ι → Y → HolderMap X ℂ α} (hf : ∀ i, ContDiff ℝ n (f i)) :
    ContDiff ℝ n (fun y ↦ HolderMap.listProduct hα l (fun i ↦ f i y)) := by
  induction l with
  | nil => exact contDiff_const
  | cons i l ih =>
    have hp : ContDiff ℝ n (fun y : Y ↦ (f i y, HolderMap.listProduct hα l (fun j ↦ f j y))) :=
      (hf i).prodMk ih
    change ContDiff ℝ n ((fun p : HolderMap X ℂ α × HolderMap X ℂ α ↦
      HolderMap.bilinear hα (ContinuousLinearMap.mul ℝ ℂ) p.1 p.2) ∘
      (fun y : Y ↦ (f i y, HolderMap.listProduct hα l (fun j ↦ f j y))))
    exact (HolderMap.contDiff_bilinear (X := X) hα (ContinuousLinearMap.mul ℝ ℂ) n).comp hp

/-- The pointwise finite product, retaining the Hölder Banach topology. -/
def finiteProduct (hα : 0 ≤ α) (s : Finset ι) (f : ι → HolderMap X ℂ α) : HolderMap X ℂ α :=
  HolderMap.listProduct hα s.toList f

@[simp] theorem value_finiteProduct (hα : 0 ≤ α) (s : Finset ι)
    (f : ι → HolderMap X ℂ α) (x : X) :
    HolderMap.value (HolderMap.finiteProduct hα s f) x = ∏ i ∈ s, HolderMap.value (f i) x := by
  rw [HolderMap.finiteProduct, HolderMap.value_listProduct, Finset.prod_map_toList]

theorem contDiff_finiteProduct (hα : 0 ≤ α) (s : Finset ι) (n : ℕ∞ω)
    {f : ι → Y → HolderMap X ℂ α} (hf : ∀ i, ContDiff ℝ n (f i)) :
    ContDiff ℝ n (fun y ↦ HolderMap.finiteProduct hα s (fun i ↦ f i y)) :=
  HolderMap.contDiff_listProduct hα s.toList n hf

end ComplexProducts
end OAI.Analysis.Normed.Function.Holder.HolderMap
