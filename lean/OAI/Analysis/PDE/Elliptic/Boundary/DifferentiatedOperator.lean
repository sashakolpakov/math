import OAI.Analysis.PDE.Elliptic.Boundary.Third.NormalRecovery

/-! Exact differentiation of the real elliptic equation used in the
second boundary bootstrap. All derivatives are actual Fréchet derivatives. -/

noncomputable section
open Filter Set
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem hasDerivAt_hessian_component_path
    {u : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 3 u)
    (x v e₁ e₂ : EuclideanSpace ℝ I) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ u) (x+s • v) e₁ e₂)
      (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)) (x+t • v) e₁ e₂) t := by
  have h₁ := OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 2) (by norm_num) e₂
  have h₂ := OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative h₁ (m := 1) (by norm_num) e₁
  have hd := OAI.Analysis.PDE.Dirichlet.hasDerivAt_directional_path (h₂.differentiable one_ne_zero) x v t
  rw [OAI.Analysis.PDE.Dirichlet.directionalDerivative_triple_comm hu] at hd
  simpa only [OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice (hu.of_le (by norm_num)),
    OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 2) (by norm_num) v)] using hd

theorem hasDerivAt_indexedOperator_path
    {u : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 3 u)
    (a : EuclideanSpace ℝ I → Matrix I I ℝ)
    (ha : ∀ i j, Differentiable ℝ (fun x => a x i j))
    (x v : EuclideanSpace ℝ I) (t : ℝ) :
    HasDerivAt (fun s : ℝ => OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a u (x+s • v))
      (OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) (x+t • v) +
        ∑ i, ∑ j, fderiv ℝ (fun z => a z i j) (x+t • v) v *
          fderiv ℝ (fderiv ℝ u) (x+t • v)
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) t := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      (OAI.Analysis.PDE.Dirichlet.hasDerivAt_directional_path (ha i j) x v t).mul
        (hasDerivAt_hessian_component_path hu x v
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) t)))
  convert hd using 1
  · ext s
    simp only [OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator, Finset.sum_apply, Pi.mul_apply]
  · simp only [OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator, OAI.Analysis.PDE.Dirichlet.directionalDerivative, Finset.sum_add_distrib]
    ring

/-- Differentiating the actual equation produces the coefficient-derivative
commutator, with its sign fixed by the product rule. -/
theorem indexed_equation_directional
    {u f : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 3 u)
    (a : EuclideanSpace ℝ I → Matrix I I ℝ)
    (ha : ∀ i j, Differentiable ℝ (fun x => a x i j))
    (x v : EuclideanSpace ℝ I) (hf : DifferentiableAt ℝ f x)
    (heq : OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a u =ᶠ[𝓝 x] f) :
    OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) x =
      fderiv ℝ f x v - ∑ i, ∑ j, fderiv ℝ (fun z => a z i j) x v *
        fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hp : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd := hasDerivAt_indexedOperator_path hu a ha x v 0
  have hF : HasDerivAt (fun t : ℝ => f (x+t • v)) (fderiv ℝ f x v) 0 := by
    exact hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have he : (fun t : ℝ => OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a u (x+t • v)) =ᶠ[𝓝 0]
      (fun t : ℝ => f (x+t • v)) := by
    exact heq.comp_tendsto (by simpa using hp.continuousAt.tendsto)
  have hv := hd.unique (hF.congr_of_eventuallyEq he)
  simp only [zero_smul, add_zero] at hv
  linarith

/-- No differentiability of the elliptic coefficient outside the point
under consideration is needed. In particular the logarithmic Moore
coefficient may be singular outside the positive domain. -/
theorem indexed_equation_directional_local_coefficient
    {u f : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 3 u)
    (a : EuclideanSpace ℝ I → Matrix I I ℝ)
    (x v : EuclideanSpace ℝ I)
    (ha : ∀ i j, DifferentiableAt ℝ (fun z => a z i j) x)
    (hf : DifferentiableAt ℝ f x)
    (heq : OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a u =ᶠ[𝓝 x] f) :
    OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) x =
      fderiv ℝ f x v - ∑ i, ∑ j, fderiv ℝ (fun z => a z i j) x v *
        fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hp : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hdA (i j : I) : HasDerivAt (fun t : ℝ => a (x+t • v) i j)
      (fderiv ℝ (fun z => a z i j) x v) 0 :=
    (ha i j).hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ => (hdA i j).mul
      (hasDerivAt_hessian_component_path hu x v
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) 0)))
  have hd' : HasDerivAt (fun t : ℝ => OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a u (x+t • v))
      (OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) x +
        ∑ i, ∑ j, fderiv ℝ (fun z => a z i j) x v *
          fderiv ℝ (fderiv ℝ u) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) 0 := by
    convert hd using 1
    · ext t
      simp only [OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator, Finset.sum_apply, Pi.mul_apply]
    · simp only [OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator, Finset.sum_add_distrib, zero_smul, add_zero]
      ring
  have hF : HasDerivAt (fun t : ℝ => f (x+t • v)) (fderiv ℝ f x v) 0 :=
    hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have he : (fun t : ℝ => OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a u (x+t • v)) =ᶠ[𝓝 0]
      (fun t : ℝ => f (x+t • v)) :=
    heq.comp_tendsto (by simpa using hp.continuousAt.tendsto)
  have hv := hd'.unique (hF.congr_of_eventuallyEq he)
  linarith

omit [DecidableEq I] in
/-- Tangential differentiation preserves homogeneous Dirichlet data in
flat coordinates. This supplies the boundary condition at each bootstrap. -/
theorem directionalDerivative_zero_on_hyperplane
    {u : EuclideanSpace ℝ I → ℝ} {U : Set (EuclideanSpace ℝ I)}
    (hU : IsOpen U) (ell : EuclideanSpace ℝ I →L[ℝ] ℝ) (c : ℝ)
    (hz : ∀ z ∈ U, ell z = c → u z = 0)
    {x v : EuclideanSpace ℝ I} (hx : x ∈ U) (hxc : ell x = c)
    (hv : ell v = 0) (hu : DifferentiableAt ℝ u x) : OAI.Analysis.PDE.Dirichlet.directionalDerivative u v x = 0 := by
  have hp : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun t : ℝ => u (x+t • v)) (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v x) 0 :=
    hu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have he : (fun t : ℝ => u (x+t • v)) =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
    have hpn : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
      simpa using hp.continuousAt.tendsto
    filter_upwards [hpn.eventually (hU.mem_nhds hx)] with t ht
    exact hz _ ht (by simp only [map_add, map_smul, hv, smul_zero, add_zero, hxc])
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq he)

omit [DecidableEq I] in
theorem second_tangential_derivative_zero_on_hyperplane
    {u : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 2 u)
    {U : Set (EuclideanSpace ℝ I)} (hU : IsOpen U)
    (ell : EuclideanSpace ℝ I →L[ℝ] ℝ) (c : ℝ)
    (hz : ∀ z ∈ U, ell z = c → u z = 0)
    {x v w : EuclideanSpace ℝ I} (hx : x ∈ U) (hxc : ell x = c)
    (hv : ell v = 0) (hw : ell w = 0) :
    OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) w x = 0 := by
  apply directionalDerivative_zero_on_hyperplane hU ell c
    (fun z hzU hzc => directionalDerivative_zero_on_hyperplane hU ell c hz hzU hzc hv
      (hu.differentiable (by norm_num) z)) hx hxc hw
  exact (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 1) (by norm_num) v).differentiable one_ne_zero x

end OAI.Analysis.PDE.Elliptic
