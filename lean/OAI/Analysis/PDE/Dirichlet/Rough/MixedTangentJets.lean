import OAI.Analysis.PDE.Dirichlet.Rough.MixedDirectional

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem reverseDirections_mem (vs : List E) (i : Fin vs.length) :
    reverseDirections vs i ∈ vs := by
  induction vs with
  | nil => exact Fin.elim0 i
  | cons v vs ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [reverseDirections, Fin.snoc_last, List.mem_cons, true_or]
      · simpa only [reverseDirections, Fin.snoc_castSucc] using List.mem_cons_of_mem v (ih j)

omit [FiniteDimensional ℝ E] in
/-- Mixed parameter derivatives along the tangent space give the actual
successive directional derivatives required by the nonlinear normal
bootstrap. The only prior regularity needed is the order being differentiated. -/
theorem contDiffOn_iterated_tangent_of_parameter_tensors
    (ℓ : E →L[ℝ] ℝ) {S : Set E} {f : E → ℝ} (vs : List E)
    (hf : ContDiff ℝ vs.length f) (hvs : ∀ v ∈ vs, ℓ v = 0)
    (ht : ∀ v : Fin vs.length → ℓ.ker,
      ContDiffOn ℝ 2 (fun z ↦ iteratedFDeriv ℝ vs.length
        (fun t : ℓ.ker ↦ f (z+(t:E))) 0 v) S) :
    ContDiffOn ℝ 2 (iteratedConstantDirectional f vs) S := by
  let v : Fin vs.length → ℓ.ker := fun i ↦
    ⟨reverseDirections vs i, hvs _ (reverseDirections_mem vs i)⟩
  apply (ht v).congr
  intro z hz
  have he := iteratedFDeriv_affine_parameter hf ℓ.ker.subtypeL z v
  exact (iteratedConstantDirectional_eq_tensor vs hf z).trans he.symm

end OAI.Analysis.PDE.Dirichlet
