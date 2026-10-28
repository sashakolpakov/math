import OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalHermitian
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Spectral

/-! # Rational Similitude Spectrum -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalSimilitudeSpectrum.Construction

noncomputable section

/-! Positive rational quadratic similitudes have complex eigenvalues of
absolute value equal to the square root of their multiplier. -/

open scoped TensorProduct InnerProductSpace

universe u v

variable {ι : Type u} [Fintype ι] {V : Type v} [AddCommGroup V] [Module ℚ V]
  [FiniteDimensional ℚ V]

theorem rationalBilinearSimilitude_eigenvalue_norm
    (b : Module.Basis ι ℚ V) (B : LinearMap.BilinForm ℚ V)
    (horth : B.IsOrthoᵢ b) (hw : ∀ i, 0 < B (b i) (b i))
    (T : Module.End ℚ V) (c : ℚ) (hT : ∀ x y, B (T x) (T y) = c * B x y)
    (z : ℂ) (hz : Module.End.HasEigenvalue (T.baseChange ℂ) z) : ‖z‖ = Real.sqrt (c : ℝ) := by
  let core := RationalHermitian.Construction.rationalOrthogonalHermitianCore b B hw
  let : NormedAddCommGroup (TensorProduct ℚ ℂ V) := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ (TensorProduct ℚ ℂ V) := InnerProductSpace.ofCore core.toCore
  have hinner (x y : TensorProduct ℚ ℂ V) :
      inner ℂ (T.baseChange ℂ x) (T.baseChange ℂ y) = (c : ℂ) * inner ℂ x y := by
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      induction y using TensorProduct.inductionOn with
      | tmul s y =>
        change WeightedHermitian.Construction.weightedHermitian (b.baseChange ℂ) (fun i => (B (b i) (b i) : ℝ))
          (r ⊗ₜ[ℚ] T x) (s ⊗ₜ[ℚ] T y) = (c : ℂ) *
          WeightedHermitian.Construction.weightedHermitian (b.baseChange ℂ) (fun i => (B (b i) (b i) : ℝ)) (r ⊗ₜ[ℚ] x) (s ⊗ₜ[ℚ] y)
        rw [RationalHermitian.Construction.rationalOrthogonalHermitian_tmul b B horth, RationalHermitian.Construction.rationalOrthogonalHermitian_tmul b B horth, hT]
        push_cast
        ring
      | add y y' hy hy' => simp only [map_add, inner_add_right, mul_add, hy, hy']
    | add x x' hx hx' => simp only [map_add, inner_add_left, mul_add, hx, hx']
  have hadj : (T.baseChange ℂ).adjoint.comp (T.baseChange ℂ) =
      ((c : ℝ) : ℂ) • LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro x
    change inner ℂ x ((T.baseChange ℂ).adjoint (T.baseChange ℂ y)) =
      inner ℂ x (((c : ℝ) : ℂ) • y)
    rw [LinearMap.adjoint_inner_right, hinner, inner_smul_right]
    norm_cast
  exact Spectral.Construction.eigenvalue_norm_of_adjoint_comp (T.baseChange ℂ) (c : ℝ) hadj z hz

theorem rationalQuadraticSimilitude_eigenvalue_norm
    (Q : QuadraticForm ℚ V) (hQ : Q.PosDef)
    (T : Module.End ℚ V) (c : ℚ) (hT : ∀ x, Q (T x) = c * Q x)
    (z : ℂ) (hz : Module.End.HasEigenvalue (T.baseChange ℂ) z) : ‖z‖ = Real.sqrt (c : ℝ) := by
  let B := QuadraticMap.associatedHom ℚ Q
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (Q.associated_isSymm ℚ)
  have hw (i) : 0 < B (b i) (b i) := by
    rw [show B (b i) (b i) = Q (b i) from QuadraticMap.associated_eq_self_apply ℚ Q (b i)]
    exact hQ _ (b.ne_zero i)
  have he : Q.comp T = c • Q := QuadraticMap.ext hT
  have hB (x y : V) : B (T x) (T y) = c * B x y := by
    have h := congrArg (QuadraticMap.associatedHom ℚ) he
    rw [QuadraticMap.associated_comp, map_smul] at h
    exact congrArg (fun C : LinearMap.BilinForm ℚ V => C x y) h
  exact rationalBilinearSimilitude_eigenvalue_norm b B hb hw T c hB z hz

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalSimilitudeSpectrum.Construction
