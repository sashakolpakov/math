import OAI.RepresentationTheory.Theta.Geometric.Period.Algebraization

/-! # Period Eq -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Rational special-unitary matrices act on both embedding summands of
the actual reference ambient space. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.rationalAtEmbedding (σ : E →+* ℂ) (g : D.RationalSU) : Period.Quotient.PeriodBlock ≃ₗ[ℂ] Period.Quotient.PeriodBlock :=
  Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map σ g.val)

def Data.ActiveHeckeThetaData.rationalAmbient (g : D.RationalSU) :
    Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) :=
  LinearEquiv.piCongrRight fun i =>
    (D.rationalAtEmbedding (D.pel.reference.embeddings i).toRingHom g).prodCongr
      (D.rationalAtEmbedding (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (D.pel.reference.embeddings i)).toRingHom g)

theorem Data.ActiveHeckeThetaData.rationalAtEmbedding_coordinates (σ : E →+* ℂ) (g : D.RationalSU) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    D.rationalAtEmbedding σ g (fun j => σ (v j)) =
      fun j => σ (D.rationalLinear g v j) := by
  funext j
  exact (RingHom.map_mulVec σ g.val.val v j).symm

theorem Data.ActiveHeckeThetaData.rationalAmbient_embedding (g : D.RationalSU) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    D.rationalAmbient g (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v) =
      Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings (D.rationalLinear g v) := by
  funext i
  apply Prod.ext
  · exact D.rationalAtEmbedding_coordinates (D.pel.reference.embeddings i).toRingHom g v
  · exact D.rationalAtEmbedding_coordinates
      (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (D.pel.reference.embeddings i)).toRingHom g v

omit [NumberField.IsCMField E] in
theorem Data.ActiveHeckeThetaData.localB_eq_unitaryForm (σ : E →ₐ[ℚ] ℂ) (b : E) (u v : Period.Quotient.PeriodBlock) :
    Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => σ) (Matrix.diagonal ![1, 1, b]) () u v =
      Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd ℂ) (σ b) u (star v) := by
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal]
  simp [Geometry.ComplexBall.ArithmeticQuotientEquationsData.form, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient, Fin.sum_univ_succ, add_assoc]

theorem Data.ActiveHeckeThetaData.rationalAtEmbedding_conjugate (σ : E →ₐ[ℚ] ℂ) (g : D.RationalSU) (v : Period.Quotient.PeriodBlock) :
    D.rationalAtEmbedding (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ).toRingHom g v =
      star (D.rationalAtEmbedding σ.toRingHom g (star v)) := by
  funext j
  change ((g.val.val.map (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ)).mulVec v) j =
    star (((g.val.val.map σ).mulVec (star v)) j)
  simp [Matrix.mulVec, dotProduct, AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding]

theorem Data.ActiveHeckeThetaData.localB_rationalAtEmbedding (σ : E →ₐ[ℚ] ℂ) (g : D.RationalSU) (u v : Period.Quotient.PeriodBlock) :
    Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => σ) (Matrix.diagonal ![1, 1, D.pel.reference.b]) ()
      (D.rationalAtEmbedding σ.toRingHom g u)
      (D.rationalAtEmbedding (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ).toRingHom g v) =
    Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => σ) (Matrix.diagonal ![1, 1, D.pel.reference.b]) () u v := by
  rw [Data.ActiveHeckeThetaData.localB_eq_unitaryForm, Data.ActiveHeckeThetaData.localB_eq_unitaryForm, D.rationalAtEmbedding_conjugate, star_star]
  exact (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap D.pel.reference.b σ.toRingHom g).property u (star v)

end

section

/-! The rational matrix carries the actual period line to the line of its
fractional-linear ball image, with its nonzero denominator retained. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.rationalAtEmbedding_line (g : D.RationalSU) (x : D.domain) :
    D.rationalAtEmbedding D.pel.reference.μ g (Geometry.ComplexBall.PrescribedSignsB.lineVector x.val) =
      Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 2 x.val •
        Geometry.ComplexBall.PrescribedSignsB.lineVector (D.periodMap g x.val) := by
  have hmap : D.periodMap g x.val =
      Period.Ne.fractionalPeriodMap D.pel.reference.b D.pel.reference.μ g x.val :=
    Period.Ne.rationalPeriodPerm_eq_fractional D.pel.reference.b D.pel.reference.μ g x.val x.property
  have hrow (j : Fin 3) :
      D.rationalAtEmbedding D.pel.reference.μ g (Geometry.ComplexBall.PrescribedSignsB.lineVector x.val) j =
        Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g j x.val :=
    (Period.Ne.periodRow_eq_mulVec D.pel.reference.b D.pel.reference.μ g j x.val).symm
  have hc := Period.Ne.periodRow_last_ne_zero D.pel.reference.b D.pel.reference.μ g x
  funext j
  fin_cases j
  · change _ = Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 2 x.val * D.periodMap g x.val 0
    rw [hrow, hmap]
    change _ = Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 2 x.val *
      (Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 0 x.val /
        Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 2 x.val)
    rw [mul_comm, div_mul_cancel₀ _ hc]
    rfl
  · change _ = Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 2 x.val * D.periodMap g x.val 1
    rw [hrow, hmap]
    change _ = Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 2 x.val *
      (Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 1 x.val /
        Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 2 x.val)
    rw [mul_comm, div_mul_cancel₀ _ hc]
    rfl
  · change _ = Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 2 x.val * 1
    rw [hrow, mul_one]
    rfl

end

/-! Rational SU transport preserves the actual period kernels, including
the conjugate annihilator in the active block. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.prescribed_rationalAmbient (g : D.RationalSU) (x : D.domain)
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s))
    (hu : Geometry.ComplexBall.PrescribedSignsB.Prescribed
      (Geometry.ComplexBall.PrescribedSignsB.localB D.pel.reference.embeddings (Matrix.diagonal ![1, 1, D.pel.reference.b]))
      D.pel.reference.distinguished D.pel.reference.compactSigns x.val u) :
    Geometry.ComplexBall.PrescribedSignsB.Prescribed
      (Geometry.ComplexBall.PrescribedSignsB.localB D.pel.reference.embeddings (Matrix.diagonal ![1, 1, D.pel.reference.b]))
      D.pel.reference.distinguished D.pel.reference.compactSigns (D.periodMap g x.val)
      (D.rationalAmbient g u) := by
  intro i
  have hi := hu i
  by_cases h : i = D.pel.reference.distinguished
  · subst i
    simp only [↓reduceIte] at hi ⊢
    constructor
    · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hi.1
      change D.rationalAtEmbedding D.pel.reference.μ g (u D.pel.reference.distinguished).1 ∈ _
      rw [← ha, map_smul, D.rationalAtEmbedding_line]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
    · let B := Geometry.ComplexBall.PrescribedSignsB.matrixB D.pel.reference.embeddings
        (Matrix.diagonal ![1, 1, D.pel.reference.b]) D.pel.reference.distinguished
      let c := Period.Ne.periodRow D.pel.reference.b D.pel.reference.μ g 2 x.val
      have hc : c ≠ 0 := Period.Ne.periodRow_last_ne_zero D.pel.reference.b D.pel.reference.μ g x
      have hB₀ := D.localB_rationalAtEmbedding
        (D.pel.reference.embeddings D.pel.reference.distinguished) g
        (Geometry.ComplexBall.PrescribedSignsB.lineVector x.val) (u D.pel.reference.distinguished).2
      have hB : B (D.rationalAtEmbedding D.pel.reference.μ g (Geometry.ComplexBall.PrescribedSignsB.lineVector x.val))
        (D.rationalAtEmbedding
          (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (D.pel.reference.embeddings D.pel.reference.distinguished)).toRingHom g
          (u D.pel.reference.distinguished).2) =
        B (Geometry.ComplexBall.PrescribedSignsB.lineVector x.val) (u D.pel.reference.distinguished).2 := by
          simpa only [B, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply, Geometry.ComplexBall.PrescribedSignsB.localB, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ] using hB₀
      rw [D.rationalAtEmbedding_line, map_smul, LinearMap.smul_apply] at hB
      change c * _ = _ at hB
      have hr : B (Geometry.ComplexBall.PrescribedSignsB.lineVector x.val) (u D.pel.reference.distinguished).2 = 0 := by
        simpa only [B, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] using hi.2
      rw [hr] at hB
      have hzero := (mul_eq_zero.mp hB).resolve_left hc
      change Geometry.ComplexBall.PrescribedSignsB.localB D.pel.reference.embeddings
        (Matrix.diagonal ![1, 1, D.pel.reference.b]) D.pel.reference.distinguished
        (Geometry.ComplexBall.PrescribedSignsB.lineVector (D.periodMap g x.val))
        (D.rationalAtEmbedding (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding
          (D.pel.reference.embeddings D.pel.reference.distinguished)).toRingHom g
          (u D.pel.reference.distinguished).2) = 0
      simpa only [B, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] using hzero
  · simp only [ite_eq_right h] at hi ⊢
    cases hd : D.pel.reference.compactSigns i <;>
      simp only [hd, Bool.false_eq_true, ite_false, ite_true] at hi ⊢
    · change D.rationalAtEmbedding (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (D.pel.reference.embeddings i)).toRingHom g (u i).2 = 0
      rw [hi, map_zero]
    · change D.rationalAtEmbedding (D.pel.reference.embeddings i).toRingHom g (u i).1 = 0
      rw [hi, map_zero]

theorem Data.ActiveHeckeThetaData.rationalAmbient_period_kernel (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU)
    (x : D.domain) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) (hu : u ∈ D.pel.reference.periodFamily x.val) :
    D.rationalAmbient g u ∈ D.pel.reference.periodFamily (D.periodMap g x.val) := by
  rcases hg.reference_admissible with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hperiod⟩
  have hx : x.val ∈ D.pel.reference.domain := by rw [D.reference_domain_eq]; exact x.property
  have hy : D.periodMap g x.val ∈ D.pel.reference.domain := by
    rw [D.reference_domain_eq]
    exact D.periodMap_preserves g x.val x.property
  exact ((hperiod _ hy).1 _).mpr
    (D.prescribed_rationalAmbient g x u (((hperiod _ hx).1 u).mp hu))

end

end OAI.RepresentationTheory.Theta.Geometric
