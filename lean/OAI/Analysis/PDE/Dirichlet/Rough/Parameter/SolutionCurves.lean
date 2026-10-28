import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.Pushback

noncomputable section
open Set Metric Filter Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : CoordinateSpace n 4 → ℝ} {α : ℝ} {U : Set Z}
  {Φ : Z × CoordinateSpace n 4 → CoordinateSpace n 4}
  {B₀ f : CoordinateSpace n 4 → ℝ}
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => CoordinateSpace n 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

/-- A multi-parameter positive implicit family is the genuine geometric
pullback of the given solution. This proof never assumes norm continuity
of composition on the full Hölder space. -/
theorem exists_smooth_geometric_solution_family
    (hn : 1 ≤ n) (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) {K : Set V} (hK : IsCompact K)
    (hr : ContDiff ℝ 2 r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hB : ContDiff ℝ 2 B₀) (hBp : LatticePeriodic e b B₀)
    (ψ : E → ℝ) (hψ : ContDiffOn ℝ 2 ψ {x | r x < 0})
    (hψc : ContinuousOn ψ {x | r x ≤ 0}) (hψp : LatticePeriodic e b ψ)
    (hψpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hψbd : ∀ x, r x = 0 → ψ x = B₀ x)
    (hψeq : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = f x)
    (hbij : ∀ t ∈ U, Function.Bijective (fun x ↦ Φ (t,x)))
    (hi : ContDiffOn ℝ ∞ (fun p : Z × E ↦ ParameterDeformation.inverseFamily Φ p.1 p.2) {p | p.1 ∈ U})
    (hper : ∀ t ∈ U, ∀ l : Submodule.span ℤ (Set.range b), ∀ x,
      Φ (t,x+e.symm ((l:P),0)) = Φ (t,x)+e.symm ((l:P),0))
    (hdom : ∀ t ∈ U, ∀ x, r (Φ (t,x)) < 0 ↔ r x < 0)
    (hclosed : ∀ t ∈ U, ∀ x, r (Φ (t,x)) ≤ 0 ↔ r x ≤ 0)
    (hJ : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian t) x = ParameterDeformation.inverseJacobian Φ (t,x))
    (hT : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature t) x = ParameterDeformation.inverseHessian Φ (t,x))
    (hBg : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background t) x =
      fderiv ℝ (fderiv ℝ B₀) (Φ (t,x)))
    (hF : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source t) x = f (Φ (t,x)))
    (hα : 0 ≤ α) (hU : IsOpen U) (h0 : (0 : Z) ∈ U) (v₀ : X)
    (hzero : C.periodicOperator J hrp hα (0,v₀) = 0)
    (hder : ((fderiv ℝ (C.periodicOperator J hrp hα) (0,v₀)).comp
      (ContinuousLinearMap.inr ℝ Z X)).IsInvertible)
    (hpos : C.PositiveAt J hα (0,v₀)) :
    ∃ v : Z → X, ContDiffAt ℝ ∞ v 0 ∧ v 0 = v₀ ∧
      ∀ᶠ t in 𝓝 0, ∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.C2Holder.value (v t).val x = ψ (Φ (t,x))-B₀ (Φ (t,x)) := by
  obtain ⟨v,hv,hv0,he⟩ := C.exists_positive_implicit_family J hK hr.continuous hrp
    hbounded hα hU h0 v₀ hzero hder hpos
  refine ⟨v,hv,hv0,?_⟩
  filter_upwards [he] with t ht
  have hit : ContDiff ℝ 2 (ParameterDeformation.inverseFamily Φ t) :=
    (ParameterDeformation.contDiff_inverseFamily_slice hi ht.1).of_le (by simp)
  have hipt := ParameterDeformation.inverseFamily_preserves_domain (hbij t ht.1) (hdom t ht.1)
  have hipc := ParameterDeformation.inverseFamily_preserves_closed_domain (hbij t ht.1) (hclosed t ht.1)
  have hiv : Function.LeftInverse (ParameterDeformation.inverseFamily Φ t) (fun x ↦ Φ (t,x)) :=
    Function.leftInverse_invFun (hbij t ht.1).injective
  apply OAI.Analysis.PDE.Schauder.physicalPushback_identified_of_domain hn e b hK hr hrp hbounded hrpos hB hBp
    hψ hψc hψp hψpos hψbd hit hiv
    (fun x hx ↦ (hclosed t ht.1 x).mpr hx)
    (fun x hx ↦ (hipt x).mpr hx) (fun x hx ↦ (hipc x).mpr hx)
    (fun x hx ↦ le_antisymm ((hipc x).mpr hx.le)
      (not_lt.mp (fun h ↦ (ne_of_lt ((hipt x).mp h)) hx)))
    (fun l x ↦ ParameterDeformation.inverseFamily_equivariant t (hbij t ht.1) _ (hper t ht.1 l) x) (v t)
  · exact ParameterDeformation.parameter_pushback_positive C J hα hr.continuous hB (hbij t ht.1) hit
      (hdom t ht.1) (hJ t ht.1) (hT t ht.1) (hBg t ht.1) (v t) ht.2.2
  · intro y hy
    exact (ParameterDeformation.parameter_pushback_equation C J hα hr.continuous hrp hB ht.1 (hbij t ht.1) hit
      (hdom t ht.1) (hJ t ht.1) (hT t ht.1) (hBg t ht.1) (hF t ht.1) (v t) ht.2.1 y hy).trans
      (hψeq y hy).symm

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
