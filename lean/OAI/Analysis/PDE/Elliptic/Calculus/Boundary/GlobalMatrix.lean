import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.ChartFields
import OAI.Analysis.PDE.Dirichlet.CalculusBoundaryIsometry
import OAI.Analysis.PDE.Schauder.Dirichlet.EuclideanCoefficientHolder

/-! A genuine globally Hölder matrix representative of the transformed
coefficient on a closed convex chart patch. -/

noncomputable section
open Set
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)

theorem exists_global_chart_matrix
    (e : X ≃ₗᵢ[ℝ] E) (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 2 P)
    {S K : Set E} (hne : S.Nonempty) (hS : IsCompact S) (hconv : Convex ℝ S)
    (hGK : MapsTo G S K) (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ (A : E → E →L[ℝ] E) (a : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E) α),
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = A x) →
      ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin m) (Fin m) ℝ) α,
        ‖B‖ ≤ C*‖a‖ ∧ ∀ x, e x ∈ S → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x =
          OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.PDE.Dirichlet.isometryConjugate e
            (pullbackEllipticOperator (fderiv ℝ P (G (e x))) (A (G (e x))))) := by
  obtain ⟨C,hC,hfield⟩ := exists_chart_holder_fields_on G P hG hP hS hconv hGK hdiam hα hα1
  refine ⟨C,hC,?_⟩
  intro A a ha
  obtain ⟨b,_,hbn,_,hb,_⟩ := hfield A a ha
  let T := e ⁻¹' S
  let ι : T → S := fun x => ⟨e x,x.property⟩
  have hι : Continuous ι := by fun_prop
  let f : T → Matrix (Fin m) (Fin m) ℝ := fun x =>
    OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.PDE.Dirichlet.isometryConjugate e (OAI.Analysis.Normed.Function.Holder.HolderMap.value b (ι x)))
  have hf : Continuous f := by
    apply OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrixCLM.continuous.comp
    exact continuous_const.clm_comp (((OAI.Analysis.Normed.Function.Holder.HolderMap.value b).continuous.comp hι).clm_comp continuous_const)
  have hn (x : T) : ‖f x‖ ≤ ‖b‖ := by
    apply (OAI.Analysis.PDE.Schauder.norm_euclideanCoefficientMatrix_le _).trans
    rw [OAI.Analysis.PDE.Dirichlet.norm_isometryConjugate]
    exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le b _
  have hh (x y : T) : ‖f x-f y‖ ≤ ‖b‖*dist x y^α := by
    change ‖OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix _-OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix _‖ ≤ _
    rw [← map_sub]
    apply (OAI.Analysis.PDE.Schauder.norm_euclideanCoefficientMatrix_le _).trans
    rw [← OAI.Analysis.PDE.Dirichlet.isometryConjugate_sub,OAI.Analysis.PDE.Dirichlet.norm_isometryConjugate]
    simpa only [ι, Subtype.dist_eq, e.isometry.dist_eq] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le b (ι x) (ι y)
  have hTne : T.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨e.symm x,by simpa only [T,mem_preimage,e.apply_symm_apply] using hx⟩
  have hTc : IsComplete T := (hS.isClosed.preimage e.continuous).isComplete
  have hTconv : Convex ℝ T := hconv.linear_preimage e.toLinearEquiv.toLinearMap
  obtain ⟨B,hB,hBn⟩ := exists_convex_holder_extension_of_bounds hTne hTc hTconv hα
    (norm_nonneg b) f hf hn hh
  refine ⟨B,hBn.trans hbn,?_⟩
  intro x hx
  exact (hB ⟨x,hx⟩).trans (congrArg (fun D => OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.PDE.Dirichlet.isometryConjugate e D))
    (hb (ι ⟨x,hx⟩)))

end OAI.Analysis.PDE.Elliptic
