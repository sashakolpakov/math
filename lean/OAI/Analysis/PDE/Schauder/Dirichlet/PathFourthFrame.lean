import OAI.Analysis.PDE.Dirichlet.Fourth.PathTangent
import OAI.Analysis.PDE.Dirichlet.Fourth.ClosedEquation

noncomputable section
open Set Module
open scoped ContDiff ComplexOrder
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι I : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [Fintype I]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+1) 4
local instance fourthFrame1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthFrame1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthFrame2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthFrame2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A fixed finite periodic frame has uniform twice-tangential jets and
normal-pair equations. Both constants precede the nonlinear solution. -/
theorem InteriorThirdPathData.uniform_fourth_frame_data
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 5 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (T : I → E → E) (hT : ∀ i, ContDiff ℝ 4 (T i))
    (hTp : ∀ i, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat (T i)) (k : I)
    (htan : ∀ i, i ≠ k → ∀ x, r x=0 → fderiv ℝ r x (T i x)=0) :
    ∃ M > 0, ∃ Q > 0, ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      (∀ i, i ≠ k → ∀ j, j ≠ k → ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (d.exponent/2),
        ‖U‖ ≤ M ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u (T i)) (T j) x) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x =
          fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u (T i)) (T j)) x) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x =
          fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u (T i)) (T j))) x)) ∧
      ∃ R : I → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} ℝ (d.exponent/2),
        (∀ i, ‖R i‖ ≤ Q) ∧
        (∀ i (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.HolderMap.value (R i) x =
          OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y => OAI.Analysis.PDE.Dirichlet.detRealOperator
            (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z => B₀ z+s.u z) y))
            (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u (T i)) (T k)) x) := by
  classical
  let J := {ij : I × I // ij.1 ≠ k ∧ ij.2 ≠ k}
  have hex (ij : J) := d.uniform_second_tangent_C2Holder e lat hK hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁ (T ij.val.1) (T ij.val.2)
    (hT _) (hT _) (hTp _) (hTp _) (htan _ ij.property.1) (htan _ ij.property.2)
  choose M hM hjets using hex
  have hne : {x | r x ≤ 0}.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty {x | r x ≤ 0})
    exact ⟨x,x.property⟩
  have hrex (i : I) := d.uniform_second_background_forcing_half (by omega) e lat hK
    hr hB₀ hF₀ hF₁ hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁
    (T i) (T k) (hT i) (hT k) (hTp i) (hTp k)
  choose Q hQ hsource using hrex
  let M₀ := (∑ ij, M ij)+1
  let Q₀ := (∑ i, Q i)+1
  have hM₀ : 0 < M₀ := by
    have hs : 0 ≤ ∑ ij, M ij := Finset.sum_nonneg (fun ij _ => (hM ij).le)
    dsimp [M₀]; linarith
  have hQ₀ : 0 < Q₀ := by
    have hs : 0 ≤ ∑ i, Q i := Finset.sum_nonneg (fun i _ => (hQ i).le)
    dsimp [Q₀]; linarith
  have hMM (ij : J) : M ij ≤ M₀ := by
    have hs : M ij ≤ ∑ j, M j :=
      Finset.single_le_sum (fun j _ => (hM j).le) (Finset.mem_univ ij)
    dsimp [M₀]; linarith
  have hQQ (i : I) : Q i ≤ Q₀ := by
    have hs : Q i ≤ ∑ j, Q j :=
      Finset.single_le_sum (fun j _ => (hQ j).le) (Finset.mem_univ i)
    dsimp [Q₀]; linarith
  refine ⟨M₀,hM₀,Q₀,hQ₀,?_⟩
  intro s
  constructor
  · intro i hi j hj
    let ij : J := ⟨(i,j),hi,hj⟩
    obtain ⟨U,hUn,_,hU,hU₁,hU₂⟩ := hjets ij s
    exact ⟨U,hUn.trans (hMM ij),fun x => (hU x).symm,
      fun x => (hU₁ x).symm,fun x => (hU₂ x).symm⟩
  · choose F hF hFn using (fun i => hsource i s)
    refine ⟨fun i => (F i).val,fun i => (hFn i).trans (hQQ i),?_⟩
    intro i x
    exact (hF i x).trans (s.second_field_equation_on_closed_sublevel
      (hr.of_le (by simp)) hreg hB₀ hF₀ hF₁ (T i) (T k)
      (hT i) ((hT k).of_le (by norm_num)) x x.property).symm

end OAI.Analysis.PDE.Schauder
