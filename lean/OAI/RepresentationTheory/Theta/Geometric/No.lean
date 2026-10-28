import Mathlib

/-! # No -/

namespace OAI.RepresentationTheory.Theta.Geometric.No

noncomputable section

/-!
# GeometricTheta: reusable bridges and the independent-map diagnostic

This file does NOT claim the full GeometricTheta theorem. Its initial specification
left `ActiveHeckeThetaData` and its geometric predicates undefined. Interpreting
`HasAdelicThetaThetaOneFormsThetaConstruction` as just the conjunction of the supplied AdelicTheta
and ThetaOneForms outputs is insufficient. AdelicTheta has a linear map from a complex
Schwartz module; ThetaOneForms has an independently parameterized input type and
input-to-form function, with no equation identifying the two constructions.
`Theta` now constructs the actual PoissonAutomorphy/DerivativeFactorization input map and proves the
ThetaOneForms identification by derivative uniqueness; `Descent` constructs the
map to invariant holomorphic sections. No new identification hypothesis is
needed for these canonical maps. The example below remains a diagnostic
for using independently supplied maps instead of those constructions.

The first two lemmas verify the strong-approximation and finite-trace
steps without using any statement stub. The latter explicitly exhibits
the missing identification with a linear map. The final counterexample
shows that rational covariance, holomorphic dependence on the period,
and pointwise spanning do not imply the scalar covariance demanded by
GeometricTheta, even for the Hecke element twice the identity. This is an obstruction
to using only the disconnected input interfaces, not a counterexample to
the manuscript's canonically constructed theta series.

Arithmetic supplies density (the target's comment mistakenly says ElementaryDivisors). ElementaryDivisors's
Smith/determinant conclusions and TateComparison's lattice/convolution conclusions
do not identify the AdelicTheta and ThetaOneForms theta maps. PoissonAutomorphy is about the concrete
Schrodinger theta construction and likewise requires this identification
before it can constrain ThetaOneForms's independently supplied function.
-/

/-- The precise use of Arithmetic: realize an active left coset while satisfying
the open level condition away from the active place. -/
theorem rational_representative_of_Arithmetic
    {GQ Gq Ga : Type*}
    [Group Gq] [TopologicalSpace Gq] [IsTopologicalGroup Gq]
    [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
    (diagonal : GQ → Gq × Ga)
    (h_Arithmetic : DenseRange diagonal)
    (Kq : OpenSubgroup Gq) (Ka : OpenSubgroup Ga) (g : Gq) :
    ∃ γ : GQ,
      (diagonal γ).1 * g⁻¹ ∈ Kq ∧ (diagonal γ).2 ∈ Ka := by
  have hopen : IsOpen
      {x : Gq × Ga | x.1 * g⁻¹ ∈ Kq ∧ x.2 ∈ Ka} :=
    (Kq.isOpen.preimage (continuous_fst.mul_const g⁻¹)).inter
      (Ka.isOpen.preimage continuous_snd)
  apply h_Arithmetic.exists_mem_open hopen
  exact ⟨(g, 1), by simp⟩

/-- Rational covariance passes through a finite geometric trace once the
descended theta map is identified with the linear construction.

`h_ThetaOneForms` is the inverse-input version of rational pullback covariance.
`h_TateComparison` is the branch-trace formula. `h_theta_identification` is the
bridge not expressed by the two independently parameterized statements;
it is explicit here, not assumed inside an opaque data structure. -/
theorem finite_trace_covariance
    {I G S V : Type*} [Fintype I]
    [AddCommGroup S] [Module ℂ S]
    [AddCommGroup V] [Module ℂ V]
    (theta : S → V)
    (linearTheta : S →ₗ[ℂ] V)
    (h_theta_identification : ∀ φ, theta φ = linearTheta φ)
    (finiteInverse : G → S →ₗ[ℂ] S)
    (pullback : G → V →ₗ[ℂ] V)
    (h_ThetaOneForms : ∀ γ φ,
      pullback γ (theta φ) = theta (finiteInverse γ φ))
    (representatives : I → G)
    (geometricTrace : V →ₗ[ℂ] V)
    (h_TateComparison : ∀ ω,
      geometricTrace ω = ∑ i, pullback (representatives i) ω)
    (φ : S) :
    geometricTrace (theta φ) =
      theta (∑ i, finiteInverse (representatives i) φ) := by
  rw [h_TateComparison]
  simp_rw [h_ThetaOneForms]
  simp only [h_theta_identification, map_sum]

/-- Applying GeometricTheta's intertwining identity to scalar multiples of the
identity already forces scalar compatibility of the theta map. -/
theorem scalar_compatibility_of_hecke_covariance
    {A S V : Type*} [Semiring A] [Algebra ℂ A]
    [AddCommGroup S] [Module ℂ S]
    [AddCommGroup V] [Module ℂ V]
    (rho : A →ₐ[ℂ] Module.End ℂ S)
    (tau : A →ₐ[ℂ] Module.End ℂ V)
    (theta : S → V)
    (h_covariance : ∀ a φ, tau a (theta φ) = theta (rho a φ))
    (c : ℂ) (φ : S) : theta (c • φ) = c • theta φ := by
  have h := h_covariance (algebraMap ℂ A c) φ
  simpa only [AlgHom.commutes, Module.algebraMap_end_apply] using h.symm

/-- Two coordinates are enough to retain the ball's cotangent dimension. -/
abbrev Coordinates := Fin 2 → ℂ

/-- A surjectivity/spanning-friendly nonlinear reparameterization. -/
def cubeInput (φ : Coordinates) : Coordinates := fun i => φ i ^ 3

def nonlinearForms (φ : Coordinates) (_period : Coordinates) : Coordinates :=
  cubeInput φ

/-- Rational covariance can hold without input linearity: both rational
actions here are trivial. This statement holds for any rational group. -/
theorem nonlinear_rational_covariance
    {G : Type*} [Group G] (_γ : G) (φ : Coordinates) :
    (LinearEquiv.refl ℂ Coordinates)
        (cubeInput ((LinearEquiv.refl ℂ Coordinates) φ)) =
      cubeInput φ := by
  rfl

theorem nonlinear_period_holomorphic (φ : Coordinates) :
    Differentiable ℂ (nonlinearForms φ) := by
  exact differentiable_const _

/-- The nonlinear family nevertheless spans every cotangent fiber. -/
theorem nonlinear_fiber_span (z : Coordinates) :
    Submodule.span ℂ (Set.range fun φ => nonlinearForms φ z) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℂ (Fin 2)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, ?_⟩
  ext j
  simp [nonlinearForms, cubeInput, Pi.basisFun_apply, Pi.single_apply]

/-- Twice the identity in any unital complex Hecke algebra acts by 2 on
both modules. The nonlinear family fails the required intertwining. -/
theorem nonlinear_fails_twice_identity :
    (2 : ℂ) • cubeInput (fun _ => 1) ≠
      cubeInput ((2 : ℂ) • (fun _ : Fin 2 => (1 : ℂ))) := by
  intro h
  have hzero := congrFun h 0
  norm_num [cubeInput] at hzero

/-- In particular, the missing linear identification cannot be constructed
from covariance, period holomorphy, and pointwise spanning alone. -/
theorem nonlinear_has_no_linear_identification :
    ¬ ∃ L : Coordinates →ₗ[ℂ] Coordinates,
      ∀ φ, cubeInput φ = L φ := by
  rintro ⟨L, hL⟩
  apply nonlinear_fails_twice_identity
  rw [hL, hL, map_smul]

end

end OAI.RepresentationTheory.Theta.Geometric.No
