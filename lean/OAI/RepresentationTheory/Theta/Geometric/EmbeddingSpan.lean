import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodEq
import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition

/-! # Embedding Span -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Geometric.EmbeddingSpan

/-! The original paired CM embedding coordinates span the entire complex
ambient space. This uses the actual embeddings of the number field. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM

variable {E Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))

def pairedEmbeddingEquiv : ((E →ₐ[ℚ] ℂ) → Geometry.ComplexBall.PrescribedSignsB.Vec) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient Place :=
  let e := Equiv.ofBijective _ hσ
  { toFun := fun f τ => (f (σ τ), f (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ)))
    invFun := fun u ρ => if (e.symm ρ).2 then (u (e.symm ρ).1).2 else (u (e.symm ρ).1).1
    left_inv := by
      intro f
      funext ρ
      obtain ⟨⟨τ, b⟩, rfl⟩ := e.surjective ρ
      simp only [Equiv.symm_apply_apply]
      cases b <;> rfl
    right_inv := by
      intro u
      funext τ
      have h₀ : e.symm (σ τ) = (τ, false) := e.symm_apply_apply (τ, false)
      have h₁ : e.symm (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ)) = (τ, true) := e.symm_apply_apply (τ, true)
      simp [h₀, h₁]
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def complexRankThreeEmbeddings : (ℂ ⊗[ℚ] (Fin 3 → E)) ≃ₗ[ℂ] ((E →ₐ[ℚ] ℂ) → Geometry.ComplexBall.PrescribedSignsB.Vec) :=
  (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin 3 => E)).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin 3 => AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E)).trans
      { toFun := fun f ρ j => f j ρ
        invFun := fun f j ρ => f ρ j
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })

def pairedComplexification : (ℂ ⊗[ℚ] (Fin 3 → E)) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient Place :=
  (complexRankThreeEmbeddings (E := E)).trans (pairedEmbeddingEquiv σ hσ)

theorem pairedComplexification_tmul (z : ℂ) (v : Fin 3 → E) :
    pairedComplexification σ hσ (z ⊗ₜ[ℚ] v) = z • Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ v := by
  ext τ j <;> simp [pairedComplexification, complexRankThreeEmbeddings,
    pairedEmbeddingEquiv, TensorProduct.piRightHom_tmul, Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]

include hσ in
theorem embeddingCoordinates_span :
    Submodule.span ℂ (Set.range (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ)) = ⊤ := by
  apply top_unique
  intro u hu
  clear hu
  obtain ⟨t, rfl⟩ := (pairedComplexification σ hσ).surjective u
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | tmul z v =>
    rw [pairedComplexification_tmul]
    exact Submodule.smul_mem _ z (Submodule.subset_span ⟨v, rfl⟩)

include hσ in
theorem embeddingCoordinates_linear_ext {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f g : Geometry.ComplexBall.PrescribedSignsB.Ambient Place →ₗ[ℂ] W)
    (h : ∀ v, f (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ v) = g (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ v)) : f = g := by
  apply LinearMap.ext_on (embeddingCoordinates_span σ hσ)
  rintro _ ⟨v, rfl⟩
  exact h v

end RepresentationTheory.Theta.Geometric.EmbeddingSpan

namespace RepresentationTheory.Theta.Geometric

/-! The active line in the original period kernel determines the ball
point, including its affine normalization. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM

theorem EmbeddingSpan.lineVector_eq_of_mem_span (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (h : Geometry.ComplexBall.PrescribedSignsB.lineVector z ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w}) : z = w := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have hlast := congrFun ha 2
  have hone : a = 1 := by simpa [Geometry.ComplexBall.PrescribedSignsB.lineVector] using hlast
  subst a
  rw [one_smul] at ha
  funext i
  fin_cases i
  · simpa [Geometry.ComplexBall.PrescribedSignsB.lineVector] using (congrFun ha 0).symm
  · simpa [Geometry.ComplexBall.PrescribedSignsB.lineVector] using (congrFun ha 1).symm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU) (x y : D.domain)

include hg in
theorem Data.ActiveHeckeThetaData.periodPoint_of_kernel
    (h : ∀ u ∈ D.pel.reference.periodFamily x.val,
      D.rationalAmbient g u ∈ D.pel.reference.periodFamily y.val) :
    y.val = D.periodMap g x.val := by
  classical
  rcases hg.reference_admissible with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hperiod⟩
  have hx : x.val ∈ D.pel.reference.domain := by rw [D.reference_domain_eq]; exact x.property
  have hy : y.val ∈ D.pel.reference.domain := by rw [D.reference_domain_eq]; exact y.property
  let u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) :=
    Pi.single D.pel.reference.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector x.val, 0)
  have hu : u ∈ D.pel.reference.periodFamily x.val := by
    apply ((hperiod _ hx).1 u).mpr
    intro τ
    by_cases hτ : τ = D.pel.reference.distinguished
    · subst τ
      simp only [u, Pi.single_eq_same, ↓reduceIte]
      exact ⟨Submodule.subset_span (Set.mem_singleton _), by simp [Geometry.ComplexBall.PrescribedSignsB.localB]⟩
    · simp [u, hτ]
  have hv := (((hperiod _ hy).1 _).mp (h u hu)) D.pel.reference.distinguished
  simp only [↓reduceIte] at hv
  have hline : D.rationalAtEmbedding D.pel.reference.μ g (Geometry.ComplexBall.PrescribedSignsB.lineVector x.val) ∈
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector y.val} := by
    simpa only [Data.ActiveHeckeThetaData.rationalAmbient, LinearEquiv.piCongrRight_apply,
      LinearEquiv.prodCongr_apply, u, Pi.single_eq_same, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ] using hv.1
  rw [D.rationalAtEmbedding_line] at hline
  have hc := Period.Ne.periodRow_last_ne_zero D.pel.reference.b D.pel.reference.μ g x
  exact (EmbeddingSpan.lineVector_eq_of_mem_span _ _
    ((Submodule.smul_mem_iff _ hc).mp hline)).symm

end RepresentationTheory.Theta.Geometric

end

end OAI
