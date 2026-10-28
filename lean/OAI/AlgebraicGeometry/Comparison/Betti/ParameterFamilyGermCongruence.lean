import OAI.AlgebraicGeometry.Comparison.Betti.OperatorParameterJets

/-! # Parameter Family Germ Congruence -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ParameterFamilyGermCongruence.Dolbeault

noncomputable section

/-! Agreement of entire parameter slices near one parameter determines
all actual mixed jets, including those of the original Cauchy polynomials. -/

open Filter
open scoped _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem parameterJet_eq_of_family_germ {g h : P × ℂ → F} {p : P}
    (he : ∀ᶠ t in 𝓝 p, ∀ z, g (t, z) = h (t, z)) (k : ℕ) (z : ℂ) :
    OperatorParameterJets.Dolbeault.parameterJet g k (p, z) = OperatorParameterJets.Dolbeault.parameterJet h k (p, z) := by
  have hj : g =ᶠ[𝓝 (p, z)] h := by
    have hfirst : Tendsto (Prod.fst : P × ℂ → P) (𝓝 (p, z)) (𝓝 p) := continuousAt_fst
    filter_upwards [hfirst.eventually he] with y hy
    exact hy y.2
  unfold OperatorParameterJets.Dolbeault.parameterJet
  rw [(hj.iteratedFDeriv ℝ k).self_of_nhds]

omit [NormedSpace ℝ P] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem cauchyParameterPolynomial_family_germ {g h : P × ℂ → F} {p : P}
    (he : ∀ᶠ t in 𝓝 p, ∀ z, g (t, z) = h (t, z)) (c : ℂ) (r : ℝ) (N : ℕ) :
    ∀ᶠ t in 𝓝 p, ∀ z,
      Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N (t, z) = Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial h c r N (t, z) := by
  filter_upwards [he] with t ht
  have hf : (fun w => g (t, w)) = fun w => h (t, w) := funext ht
  intro z
  unfold Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial
  rw [hf]

theorem mixedParameterJet_eq_of_family_germ {g h : P × ℂ → F} {p : P}
    (he : ∀ᶠ t in 𝓝 p, ∀ z, g (t, z) = h (t, z)) (k l : ℕ) (z : ℂ) :
    iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet g k (p, w)) z =
      iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet h k (p, w)) z := by
  have hf : (fun w => OperatorParameterJets.Dolbeault.parameterJet g k (p, w)) = fun w => OperatorParameterJets.Dolbeault.parameterJet h k (p, w) :=
    funext (parameterJet_eq_of_family_germ he k)
  rw [hf]

theorem cauchyPolynomial_mixedJet_eq_of_family_germ {g h : P × ℂ → F} {p : P}
    (he : ∀ᶠ t in 𝓝 p, ∀ z, g (t, z) = h (t, z))
    (c : ℂ) (r : ℝ) (N k l : ℕ) (z : ℂ) :
    iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) k (p, w)) z =
      iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial h c r N) k (p, w)) z :=
  mixedParameterJet_eq_of_family_germ (cauchyParameterPolynomial_family_germ he c r N) k l z

end

end OAI.AlgebraicGeometry.Comparison.Betti.ParameterFamilyGermCongruence.Dolbeault
