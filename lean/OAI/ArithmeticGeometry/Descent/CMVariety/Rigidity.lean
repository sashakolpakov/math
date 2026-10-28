import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType

/-! # Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.Rigidity.Abelian

noncomputable section

/-!
The linear rigidity calculation for the enhanced-moduli route to CMAbelianVariety.
It concerns the actual CM field action on a weight-one Hodge structure.
The passage from this calculation to an algebraic moduli scheme is not
assumed here and remains a separate geometric construction.
-/

open OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM

/-- In weight one the holomorphic subspace determines the antiholomorphic
subspace by coefficient conjugation. -/
theorem weightOne_eq_of_holomorphic_eq
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H J : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V) (hh : H.holomorphic = J.holomorphic) : H = J := by
  have ha : H.antiholomorphic = J.antiholomorphic := by
    ext x
    have hH := H.conjugate_mem (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation V x)
    have hJ := J.conjugate_mem (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation V x)
    simp only [AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] at hH hJ
    rw [hH, hJ, hh]
  rcases H with ⟨_, _, _, _⟩
  rcases J with ⟨_, _, _, _⟩
  dsimp only at hh ha
  cases hh
  cases ha
  rfl

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
variable {U : Type*} [AddCommGroup U] [Module ℚ U]
  [Module E U] [IsScalarTower ℚ E U]
variable {H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U}

omit [NumberField E] [IsScalarTower ℚ E U] in
/-- Commutation with the CM field action preserves every embedding space. -/
theorem commuting_map_preserves_embeddingSpace
    (f : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U →ₗ[ℂ] AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U)
    (hf : ∀ (a : E) (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U),
      f ((AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ x) =
        (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ (f x))
    (σ : E →ₐ[ℚ] ℂ) {x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U}
    (hx : x ∈ AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ) :
    f x ∈ AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ := by
  apply (AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E U σ (f x)).mpr
  intro a
  rw [← hf, (AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E U σ x).mp hx a, map_smul]

/-- A CM-equivariant infinitesimal variation from the holomorphic subspace
to the antiholomorphic subspace, extended by zero, vanishes in rank one. -/
theorem rankOne_CM_infinitesimal_rigidity
    (h : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (f : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U →ₗ[ℂ] AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U)
    (hf : ∀ (a : E) (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U),
      f ((AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ x) =
        (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ (f x))
    (hhol : ∀ x ∈ H.holomorphic, f x ∈ H.antiholomorphic)
    (hanti : ∀ x ∈ H.antiholomorphic, f x = 0) : f = 0 := by
  apply h.embeddingBasis.ext
  intro σ
  have hv : h.embeddingBasis σ ∈ AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ :=
    (AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E U σ _).mpr (fun a => h.embeddingBasis_eigen a σ)
  rcases h.embeddingSpace_hodge_dichotomy σ with hσ | hσ
  · have hfx : f (h.embeddingBasis σ) ∈ H.holomorphic ⊓ H.antiholomorphic :=
      ⟨hσ (commuting_map_preserves_embeddingSpace f hf σ hv), hhol _ (hσ hv)⟩
    rw [H.complementary.inf_eq_bot] at hfx
    exact hfx
  · exact hanti _ (hσ hv)

/-- The actual tangent-space version: a linear map from the holomorphic
subspace to the antiholomorphic subspace commuting with the CM action is zero. -/
theorem rankOne_CM_hodge_tangent_rigidity
    (h : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (f : H.holomorphic →ₗ[ℂ] H.antiholomorphic)
    (hf : ∀ (a : E) (x : H.holomorphic),
      (f ⟨(AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ x,
        h.hodge_action a x x.property⟩ : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U) =
        (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ (f x)) : f = 0 := by
  let P := H.holomorphic.projectionOnto H.antiholomorphic H.complementary
  let F := H.antiholomorphic.subtype.comp (f.comp P)
  have hF : F = 0 := rankOne_CM_infinitesimal_rigidity h F
    (fun a x => by
      have hP : P ((AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ x) =
          ⟨(AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ (P x),
            h.hodge_action a (P x) (P x).property⟩ := by
        apply Subtype.ext
        exact AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.projection_commutes_of_preserves H.complementary
          ((AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ)
          (h.hodge_action a) (fun y hy => (h.hodge_action a).map_antiholomorphic hy) x
      change (f (P ((AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ x)) : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U) = _
      rw [hP]
      exact hf a (P x))
    (fun x _ => (f (P x)).property)
    (fun x hx => by
      change (f (P x) : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U) = 0
      rw [show P x = 0 from
        Submodule.projectionOnto_apply_of_mem_right H.complementary hx]
      simp)
  ext x
  have hx := LinearMap.congr_fun hF (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U)
  change (f (P x) : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U) = 0 at hx
  simpa only [P, Submodule.projectionOnto_apply_left, LinearMap.zero_apply,
    Submodule.coe_zero] using hx

/-- Inclusion of the sets of holomorphic embedding lines gives inclusion
of the whole holomorphic subspaces. -/
theorem rankOne_holomorphic_le_of_embedding_types
    (h : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) {J : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U}
    (hHJ : ∀ σ : E →ₐ[ℚ] ℂ,
      AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ H.holomorphic →
        AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ J.holomorphic) :
    H.holomorphic ≤ J.holomorphic := by
  rw [h.holomorphic_eq_span_embeddingBasis]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ, hσ, rfl⟩
  have hv : h.embeddingBasis σ ∈ AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ :=
    (AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E U σ _).mpr (fun a => h.embeddingBasis_eigen a σ)
  apply hHJ σ _ hv
  rw [h.embeddingSpace_eq_span]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr
    ((h.embeddingBasis_mem_holomorphic_iff σ).mpr hσ)

/-- The possible weight-one CM Hodge structures for a fixed rational
rank-one module with a fixed CM-field action. -/
def RankOneCMPeriod (E U : Type*) [Field E] [Algebra ℚ E]
    [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U] :=
  {H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U // AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.RankOneCMAction E H}

/-- Record which embedding lines are holomorphic, independently of a
choice of a generator of the rank-one module. -/
def rankOnePeriodTypes (P : RankOneCMPeriod E U) : Set (E →ₐ[ℚ] ℂ) :=
  {σ | AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ P.val.holomorphic}

/-- The embedding types determine the entire CM Hodge structure. -/
theorem rankOnePeriodTypes_injective :
    Function.Injective (rankOnePeriodTypes (E := E) (U := U)) := by
  intro P Q hPQ
  have hh : P.val.holomorphic = Q.val.holomorphic := by
    apply le_antisymm
    · apply rankOne_holomorphic_le_of_embedding_types P.property
      intro σ hσ
      exact (show σ ∈ rankOnePeriodTypes Q from hPQ ▸ hσ)
    · apply rankOne_holomorphic_le_of_embedding_types Q.property
      intro σ hσ
      exact (show σ ∈ rankOnePeriodTypes P from hPQ.symm ▸ hσ)
  exact Subtype.ext (weightOne_eq_of_holomorphic_eq P.val Q.val hh)

/-- There are only finitely many CM periods with a fixed rank-one
CM-field action. This is the discrete-period calculation used by the
enhanced-moduli argument. -/
theorem rankOne_CM_periods_finite : Finite (RankOneCMPeriod E U) :=
  Finite.of_injective rankOnePeriodTypes rankOnePeriodTypes_injective

end

end OAI.ArithmeticGeometry.Descent.CMVariety.Rigidity.Abelian
