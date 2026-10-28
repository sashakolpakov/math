import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF
import Mathlib.Analysis.Analytic.Order
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Directional Jets On -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.DirectionalJetsOn.Constructions.DirectionalJets

noncomputable section

/-!
# RiemannProjectivity: directional jets detect nonflat holomorphic zeros

Repeated directional derivatives remain holomorphic. Along an affine
complex line they agree with ordinary iterated derivatives. A finite order
zero on such a line therefore lies on a regular zero set of one of the
directional derivatives.
-/

open Set Filter
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def jet (f : V → ℂ) (v : V) : ℕ → V → ℂ
  | 0 => f
  | n + 1 => fun x => fderiv ℂ (jet f v n) x v

theorem differentiableOn_jet {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (v : V) (n : ℕ) :
    DifferentiableOn ℂ (DirectionalJets.jet f v n) U := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact fun x hx => (HolomorphicContourF.Constructions.HolomorphicDerivative.differentiableAt_directionalDerivative hU ih hx v).differentiableWithinAt

theorem jet_eq_iteratedDeriv {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (x v : V) (n : ℕ)
    {c : ℂ} (hc : x + c • v ∈ U) :
    iteratedDeriv n (fun t : ℂ => f (x + t • v)) c = DirectionalJets.jet f v n (x + c • v) := by
  have hline : Differentiable ℂ (fun t : ℂ => x + t • v) :=
    (differentiable_id.smul_const v).const_add x
  have hnear : (fun t : ℂ => x + t • v) ⁻¹' U ∈ 𝓝 c :=
    (hU.preimage hline.continuous).mem_nhds hc
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    have heq : iteratedDeriv n (fun t : ℂ => f (x + t • v)) =ᶠ[𝓝 c]
        (fun t => DirectionalJets.jet f v n (x + t • v)) := by
      filter_upwards [hnear] with t ht
      exact ih ht ((hU.preimage hline.continuous).mem_nhds ht)
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd := (((differentiableOn_jet hU hf v n) _ hc).differentiableAt
      (hU.mem_nhds hc)).hasFDerivAt
    simpa only [DirectionalJets.jet, Function.comp_def, id_eq, one_smul] using!
      (hd.comp_hasDerivAt c (((hasDerivAt_id c).smul_const v).const_add x)).deriv

theorem exists_regular_jet_of_nonzero_line {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : V} (hx : x ∈ U)
    (hzero : f x = 0) (v : V)
    (hnot : ¬∀ᶠ t : ℂ in 𝓝 0, f (x + t • v) = 0) :
    ∃ n : ℕ, DirectionalJets.jet f v n x = 0 ∧ Function.Surjective (fderiv ℂ (DirectionalJets.jet f v n) x) := by
  let g : ℂ → ℂ := fun t => f (x + t • v)
  have hline : Differentiable ℂ (fun t : ℂ => x + t • v) :=
    (differentiable_id.smul_const v).const_add x
  have hnear : (fun t : ℂ => x + t • v) ⁻¹' U ∈ 𝓝 0 :=
    (hU.preimage hline.continuous).mem_nhds (by simpa using hx)
  have hga : AnalyticAt ℂ g 0 :=
    (hf.comp hline.differentiableOn (mapsTo_preimage _ _)).analyticAt hnear
  have horder : analyticOrderAt g 0 ≠ ⊤ := fun h => hnot (analyticOrderAt_eq_top.mp h)
  have hnat := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hga).mp
    (Nat.cast_analyticOrderNatAt horder).symm
  rcases hN : analyticOrderNatAt g 0 with _ | n
  · have h := hnat.2
    rw [hN] at h
    exact False.elim (h (by simpa only [iteratedDeriv_zero, g, zero_smul, add_zero] using hzero))
  · have hnj : iteratedDeriv n g 0 = 0 := hnat.1 n (by omega)
    have hsj : iteratedDeriv (n + 1) g 0 ≠ 0 := by simpa only [hN] using hnat.2
    have hjet (m : ℕ) : iteratedDeriv m g 0 = DirectionalJets.jet f v m x := by
      simpa only [g, zero_smul, add_zero] using jet_eq_iteratedDeriv hU hf x v m (c := 0) (by simpa using hx)
    refine ⟨n, (hjet n).symm.trans hnj, ?_⟩
    have hdne : (fderiv ℂ (DirectionalJets.jet f v n) x).toLinearMap ≠ 0 := by
      intro hd0
      apply hsj
      rw [hjet]
      change (fderiv ℂ (DirectionalJets.jet f v n) x).toLinearMap v = 0
      rw [hd0, LinearMap.zero_apply]
    exact LinearMap.surjective hdne

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.DirectionalJetsOn.Constructions.DirectionalJets
