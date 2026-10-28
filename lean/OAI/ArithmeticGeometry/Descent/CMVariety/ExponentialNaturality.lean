import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM

/-! # Exponential Naturality -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialNaturality.Abelian

noncomputable section

/-!
Naturality of the constructed native exponential under differentiable
group maps. The proof pushes forward the actual invariant vector field
and uses uniqueness of its global integral curve.
-/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential
open scoped _root_.Manifold ContDiff

variable {E F G H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [TopologicalSpace H] [ChartedSpace F H] [Group H]
  [LieGroup (𝓘(ℝ, E)) ∞ G] [LieGroup (𝓘(ℝ, F)) ∞ H]

theorem groupMap_invariant_pushforward
    (f : G →* H) (hf : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) f)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (g : G) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f g (mulInvariantVectorField v g) =
      mulInvariantVectorField
        (show GroupLieAlgebra (𝓘(ℝ, F)) H from
          mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f 1 v) (f g) := by
  have hg : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) :=
    (contMDiff_mul_left (n := ∞)).mdifferentiable (by simp)
  have hfg : MDifferentiable (𝓘(ℝ, F)) (𝓘(ℝ, F)) (fun x : H => f g * x) :=
    (contMDiff_mul_left (n := ∞)).mdifferentiable (by simp)
  have he : (f : G → H) ∘ (fun x => g * x) =
      (fun x : H => f g * x) ∘ f := funext (f.map_mul g)
  have hleft := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, F)) (1 : G) (hf (g * 1)) (hg 1)
  have hright := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
    (I'' := 𝓘(ℝ, F)) (1 : G) (hfg (f 1)) (hf 1)
  rw [he, hright, mul_one] at hleft
  have h := congrArg (fun L : E →L[ℝ] F => L v) hleft
  erw [map_one] at h
  exact h.symm

theorem groupMap_integralCurve
    (f : G →* H) (hf : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) f)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) {γ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) :
    IsMIntegralCurve (f ∘ γ) (mulInvariantVectorField
      (show GroupLieAlgebra (𝓘(ℝ, F)) H from
        mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f 1 v)) := by
  intro t
  have hd := (hf (γ t)).hasMFDerivAt.comp t (hγ t)
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  let D : E →L[ℝ] F := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f (γ t)
  change D (r • mulInvariantVectorField v (γ t)) = r • _
  exact (D.map_smul r (show E from mulInvariantVectorField v (γ t))).trans
    (congrArg (r • ·) (groupMap_invariant_pushforward f hf v (γ t)))

variable [CompleteSpace E] [CompleteSpace F] [T2Space G] [T2Space H]

/-- The derivative at the identity intertwines the actual exponentials. -/
theorem groupMap_exp
    (f : G →* H) (hf : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) f)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    f (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp v) = AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (show GroupLieAlgebra (𝓘(ℝ, F)) H from
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f 1 v) := by
  let : LieGroup (𝓘(ℝ, F)) (minSmoothness ℝ 3) H := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  let w : GroupLieAlgebra (𝓘(ℝ, F)) H :=
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f 1 v
  have hw : ContMDiff (𝓘(ℝ, F)) (𝓘(ℝ, F)).tangent 1
      (fun x : H => (⟨x, mulInvariantVectorField w x⟩ : TangentBundle (𝓘(ℝ, F)) H)) :=
    (contMDiff_mulInvariantVectorField w).of_le (by simp)
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hw
    (groupMap_integralCurve f hf v (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve_integral v)) (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve_integral w)
    (t₀ := (0 : ℝ)) (by simp)
  exact congrFun he 1

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialNaturality.Abelian
