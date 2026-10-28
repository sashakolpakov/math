import OAI.Analysis.PDE.Dirichlet.Rough.GeometricIFT
import OAI.Analysis.PDE.Dirichlet.Rough.GeometricGlobal
import OAI.Analysis.PDE.Dirichlet.Rough.Moore.C2Representative

noncomputable section
open Set Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : CoordinateSpace n 4 → ℝ} {α : ℝ}
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => CoordinateSpace n 4
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

local instance roughC4DualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance roughC4DualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance roughC4SecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance roughC4SecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance roughC4C2Group : NormedAddCommGroup H := inferInstance
local instance roughC4C2Space : NormedSpace ℝ H := inferInstance
local instance roughC4C2Module : Module ℝ H := inferInstance
local instance roughC4C2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance roughC4C2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
local instance roughC4C2AddZero : AddZeroClass H := inferInstance

/-- Every positive rough C²,α solution with invertible actual Moore
derivative has a genuine global periodic C⁴ representative for smooth
data. Near a smooth base, the invertibility is supplied by the open
invertibility neighborhood, not by a circular boundary regularity claim. -/
theorem exists_periodic_C4_representative_of_invertible [Nontrivial E]
    (hn : 1 ≤ n) {K : Set V} (hK : IsCompact K)
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (B₀ f : E → ℝ) (hB₀ : ContDiff ℝ ∞ B₀) (hf : ContDiff ℝ ∞ f)
    (hB₀p : LatticePeriodic e b B₀) (hfp : LatticePeriodic e b f)
    (B : H) (hBp : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value B)))
    (hB₀v : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value B x = B₀ x)
    (hB₁ : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative B x = fderiv ℝ B₀ x)
    (hB₂ : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x = fderiv ℝ (fderiv ℝ B₀) x)
    (u : X)
    (hpos : ∀ x : {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x)).PosDef)
    (heq : ∀ x : {x | r x ≤ 0},
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x) = f x)
    (hΩ : IsOpen {x | r x < 0}) (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (hinv : (fderiv ℝ (periodicMooreDirichletOperator hΩ hclosure
      (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots B hBp) u).IsInvertible) :
    ∃ ψ : E → ℝ, ContDiff ℝ 4 ψ ∧ LatticePeriodic e b ψ ∧
      (∀ x, r x = 0 → ψ x = B₀ x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value (B+u.val) x = ψ x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (B+u.val) x = fderiv ℝ ψ x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (B+u.val) x =
        fderiv ℝ (fderiv ℝ ψ) x) ∧
      (∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) ∧
      (∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = f x) := by
  obtain ⟨v,hv,hvp,hvbd,hv₀,hv₁,hv₂⟩ := exists_full_potential_C2_representative hn hK
    hr hrp hbounded hreg B₀ (hB₀.of_le (by simp)) hB₀p B hB₀v hB₁ hB₂ u
  have hH (x : {x | r x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x :=
    quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val) v x (hv₂ x)
  have hvpos (x : E) (hx : r x ≤ 0) : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x)).PosDef := by
    rw [← hH ⟨x,hx⟩]
    exact hpos ⟨x,hx⟩
  have hveq (x : E) (hx : r x ≤ 0) : OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x) = f x := by
    rw [← hH ⟨x,hx⟩]
    exact heq ⟨x,hx⟩
  have hc := hasGeometricSolutionCurves_of_invertible hn hK hr hrp hbounded hreg hrpos
    hα hα1 B₀ f hB₀ hf hB₀p hfp B hBp hB₂ u v hv hvp hvbd hv₂ hvpos hveq hΩ hclosure hinv
  obtain ⟨ψ,hψ,hψp,hψ₀,hψ₁,hψ₂⟩ := hc.to_two.exists_periodic_C4_representative hn hK
    hr hrp hbounded hreg hv hvp hB₀ f hf hvpos hveq
  have hjet₂ (x : {x | r x ≤ 0}) : OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (B+u.val) x =
      fderiv ℝ (fderiv ℝ ψ) x := (hv₂ x).trans (hψ₂ x x.property).symm
  have hnew (x : {x | r x ≤ 0}) :=
    quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val) ψ x (hjet₂ x)
  refine ⟨ψ,hψ,hψp,(fun x hx ↦ (hψ₀ x hx.le).trans (hvbd x hx)),
    (fun x ↦ (hv₀ x).trans (hψ₀ x x.property).symm),
    (fun x ↦ (hv₁ x).trans (hψ₁ x x.property).symm),hjet₂,?_,?_⟩
  · intro x hx
    rw [← hnew ⟨x,hx⟩]
    exact hpos ⟨x,hx⟩
  · intro x hx
    rw [← hnew ⟨x,hx⟩]
    exact heq ⟨x,hx⟩

end OAI.Analysis.PDE.Dirichlet
