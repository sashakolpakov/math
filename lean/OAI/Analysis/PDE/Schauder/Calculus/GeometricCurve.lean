import OAI.Analysis.PDE.Schauder.Calculus.PositiveImplicitCurve
import OAI.Analysis.PDE.Schauder.Calculus.PushbackEquation
import OAI.Analysis.PDE.Schauder.Calculus.PushbackComparison
import OAI.Analysis.PDE.Schauder.Calculus.DomainPushback

open Set Metric Filter Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {I : Set ℝ}
  {Φ : ℝ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
  {B₀ f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

/-- The implicit branch is the actual geometric pullback, in values, even
though no continuity of composition on the full Hölder space was assumed. -/
theorem PeriodicDeformationFields.exists_smooth_geometric_curve
    (hn : 1 ≤ n) (C : PeriodicDeformationFields r α I Φ B₀ f e b)
    (J : LatticeJetLifts hΩK α e b) {K : Set V} (hK : IsCompact K)
    (hr : ContDiff ℝ 2 r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hB : ContDiff ℝ 2 B₀) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b B₀)
    (ψ : E → ℝ) (hψ : ContDiffOn ℝ 2 ψ {x | r x < 0})
    (hψc : ContinuousOn ψ {x | r x ≤ 0}) (hψp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b ψ)
    (hψpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hψbd : ∀ x, r x = 0 → ψ x = B₀ x)
    (hψeq : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = f x)
    (hbij : ∀ t ∈ I, Function.Bijective (fun x => Φ (t,x)))
    (hi : ContDiffOn ℝ ∞ (fun p : ℝ × E => OAI.Analysis.PDE.Dirichlet.inverseFamily Φ p.1 p.2) {p | p.1 ∈ I})
    (hper : ∀ t ∈ I, ∀ l : Submodule.span ℤ (Set.range b), ∀ x,
      Φ (t,x+e.symm ((l:P),0)) = Φ (t,x)+e.symm ((l:P),0))
    (hdom : ∀ t ∈ I, ∀ x, r (Φ (t,x)) < 0 ↔ r x < 0)
    (hclosed : ∀ t ∈ I, ∀ x, r (Φ (t,x)) ≤ 0 ↔ r x ≤ 0)
    (hα : 0 ≤ α) (hI : IsOpen I) (h0 : 0 ∈ I) (v₀ : X)
    (hzero : C.periodicOperator J hrp hα (0,v₀) = 0)
    (hder : ((fderiv ℝ (C.periodicOperator J hrp hα) (0,v₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ X)).IsInvertible)
    (hpos : ∀ x : {x | r x ≤ 0}, ∀ z ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
      0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.fields.hessianField hα J.first J.second (0,v₀)) x) z).re) :
    ∃ v : ℝ → X, ContDiffAt ℝ ∞ v 0 ∧ v 0 = v₀ ∧
      ∀ᶠ t in 𝓝 0, ∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.C2Holder.value (v t).val x = ψ (Φ (t,x))-B₀ (Φ (t,x)) := by
  obtain ⟨v,hv,hv0,he⟩ := C.exists_positive_implicit_curve J hK hr.continuous hrp
    hbounded hα hI h0 v₀ hzero hder hpos
  refine ⟨v,hv,hv0,?_⟩
  filter_upwards [he] with t ht
  have hit : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) :=
    (contDiff_parameter_space_slice hi ht.1).of_le (by simp)
  have hipt := inverseFamily_preserves_domain (hbij t ht.1) (hdom t ht.1)
  have hipc := inverseFamily_preserves_closed_domain (hbij t ht.1) (hclosed t ht.1)
  have hiv : Function.LeftInverse (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) (fun x => Φ (t,x)) :=
    Function.leftInverse_invFun (hbij t ht.1).injective
  apply physicalPushback_identified_of_domain hn e b hK hr hrp hbounded hrpos hB hBp
    hψ hψc hψp hψpos hψbd hit hiv
    (fun x hx => (hclosed t ht.1 x).mpr hx)
    (fun x hx => (hipt x).mpr hx) (fun x hx => (hipc x).mpr hx)
    (fun x hx => le_antisymm ((hipc x).mpr hx.le)
      (not_lt.mp (fun h => (ne_of_lt ((hipt x).mp h)) hx)))
    (fun l x => OAI.Analysis.PDE.Dirichlet.inverseFamily_equivariant t (hbij t ht.1) _ (hper t ht.1 l) x) (v t)
  · exact C.fields.pushback_positive_of_domain J hα hr.continuous hB ht.1 (hbij t ht.1) hit
      (hdom t ht.1) (v t) ht.2.2
  · intro y hy
    exact (C.pushback_equation_of_domain J hα hr.continuous hrp hB ht.1 (hbij t ht.1) hit
      (hdom t ht.1) (v t) ht.2.1 y hy).trans (hψeq y hy).symm

end OAI.Analysis.PDE.Schauder
