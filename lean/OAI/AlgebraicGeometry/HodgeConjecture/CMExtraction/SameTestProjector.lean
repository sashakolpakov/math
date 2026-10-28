import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent

/-! # Same Test Projector -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SameTestProjector

noncomputable section

section

/-!
# CMExtraction: conditional CM extraction

The explicit `ScalarTraceInput` is ScalarDescent specialized to the rational Hom
space. The original `hExtremeSlopes` supplies ExtremeSlopes's slope-to-type implications;
`htheta`, `hHodge`, and `hdecompose` already supply the needed consequences
of ThetaOneForms, GeometricTheta, and Commuting. Their full geometric statements are unnecessary
for this linear-algebraic target. RiemannProjectivity's abelian realization is unnecessary
because the conclusion only concerns rational Hodge maps from U(v).

The statement specifications are not imported or used as facts. The two
local definitions below are copied verbatim from the target specification.
-/

open scoped TensorProduct Classical
open OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent.CM OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

/-- Complex span of a coefficient-field subspace after scalar conjugation. -/
def conjugateSpace
    (K : IntermediateField ℚ ℂ)
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (A : Submodule K (K ⊗[ℚ] V))
    (σ : Gal(K/ℚ)) : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V) :=
  Submodule.span ℂ
    {y | ∃ x ∈ A,
      y = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ x)}

/-- Values on the id-line of complex scalar combinations of rational
Hodge maps from U(v), modeled by the rational vector space E. -/
def cmIdSpan
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V) :
    Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V) :=
  Submodule.span ℂ
    {y | ∃ f : E →ₗ[ℚ] V,
      ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H f ∧
      y = f.baseChange ℂ
        (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1))}

/-- The supplied ScalarDescent proposition, specialized to a rational vector space. -/
def ScalarTraceInput (K : IntermediateField ℚ ℂ)
    (W : Type*) [AddCommGroup W] [Module ℚ W] : Prop :=
  ∀ (Hpq : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification W)) (t : K ⊗[ℚ] W),
    (∀ σ : Gal(K/ℚ),
      ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K W (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K W σ t) ∈ Hpq) →
    t ∈ Submodule.span K
      {y | ∃ w : W, y = (1 : K) ⊗ₜ[ℚ] w ∧
        (1 : ℂ) ⊗ₜ[ℚ] w ∈ Hpq}

theorem descend_hom
    (K : IntermediateField ℚ ℂ)
    {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (hScalarDescent : ScalarTraceInput K (U →ₗ[ℚ] V))
    (t : K ⊗[ℚ] (U →ₗ[ℚ] V))
    (ht : ∀ σ : Gal(K/ℚ),
      ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U V
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] V) σ t) ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H J) :
    ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U V t ∈ ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan H J := by
  let S := (ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H J).comap (ComplexMultiplication.HomBaseChange.CM.homBaseChange ℂ U V)
  have hspan := hScalarDescent S t ht
  have hle : Submodule.span K
      {y | ∃ f : U →ₗ[ℚ] V, y = (1 : K) ⊗ₜ[ℚ] f ∧
        (1 : ℂ) ⊗ₜ[ℚ] f ∈ S} ≤
      ((ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan H J).restrictScalars K).comap
        (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U V) := by
    apply Submodule.span_le.mpr
    rintro y ⟨f, rfl, hf⟩
    change ComplexMultiplication.HomBaseChange.CM.homBaseChange ℂ U V ((1 : ℂ) ⊗ₜ[ℚ] f) ∈
      ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H J at hf
    have hf' : ComplexMultiplication.WeightOne.CM.IsHodgeMap H J f :=
      (ComplexMultiplication.Hodge.MapDescent.CM.baseChange_mem_hodgeHomSubspace_iff H J f).mp (by simpa using hf)
    change ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U V ((1 : K) ⊗ₜ[ℚ] f) ∈
      ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan H J
    simp only [ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients_tmul, IntermediateField.coe_one, one_smul]
    exact Submodule.subset_span ⟨f, hf', rfl⟩
  exact hle hspan

section CoefficientVectors

variable (K : IntermediateField ℚ ℂ)
variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
variable (hK : ∀ τ : E →ₐ[ℚ] ℂ, τ.fieldRange ≤ K)

def coeffVector (τ : E →ₐ[ℚ] ℂ) : K ⊗[ℚ] E :=
  (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK).symm (Pi.single τ 1)

theorem coeffVector_coordinates (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK (coeffVector K E hK τ) = Pi.single τ 1 :=
  (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK).apply_symm_apply _

theorem inclusion_coordinates (x : K ⊗[ℚ] E) (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K E x) τ =
      (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK x τ : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, IntermediateField.coe_add]

theorem inclusion_coeffVector (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K E (coeffVector K E hK τ) = ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ := by
  apply (ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E).injective
  ext υ
  rw [inclusion_coordinates K E hK, coeffVector_coordinates,
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector]
  by_cases h : τ = υ <;> simp [h]

theorem conjugate_coordinates (σ : Gal(K/ℚ)) (x : K ⊗[ℚ] E)
    (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K E σ x)
        (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ τ) =
      σ (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK x τ) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem conjugate_coeffVector (σ : Gal(K/ℚ)) (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K E σ (coeffVector K E hK τ) =
      coeffVector K E hK (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ τ) := by
  apply (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK).injective
  apply funext
  intro υ
  obtain ⟨υ, rfl⟩ := (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbeddingEquiv K E hK σ).surjective υ
  change ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK
      (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K E σ (coeffVector K E hK τ))
      (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ υ) =
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK
      (coeffVector K E hK (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ τ))
      (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ υ)
  rw [conjugate_coordinates, coeffVector_coordinates, coeffVector_coordinates]
  by_cases h : τ = υ
  · subst υ
    simp
  · have hn : ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ τ ≠
        ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ υ :=
      (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbeddingEquiv K E hK σ).injective.ne h
    simp [h, hn]

end CoefficientVectors

section LineMaps

variable (K : IntermediateField ℚ ℂ)
variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
variable (hK : ∀ τ : E →ₐ[ℚ] ℂ, τ.fieldRange ≤ K)
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A coefficient-valued map supported on one embedding line. -/
def valueLineTensor (τ : E →ₐ[ℚ] ℂ) (x : K ⊗[ℚ] V) :
    K ⊗[ℚ] (E →ₗ[ℚ] V) :=
  (ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv K E V).symm
    (((ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding K E hK τ).toLinearMap.liftBaseChange K).smulRight x)

theorem valueLineTensor_apply (τ υ : E →ₐ[ℚ] ℂ) (x : K ⊗[ℚ] V) :
    ComplexMultiplication.HomBaseChange.CM.homBaseChange K E V (valueLineTensor K E hK τ x)
        (coeffVector K E hK υ) = if υ = τ then x else 0 := by
  change ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv K E V
      ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv K E V).symm _) _ = _
  rw [LinearEquiv.apply_symm_apply, LinearMap.smulRight_apply,
    ← ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv_apply, coeffVector_coordinates]
  by_cases h : υ = τ
  · simp [h]
  · simp [h, Ne.symm h]

theorem conjugate_valueLineTensor_apply (σ : Gal(K/ℚ))
    (τ υ : E →ₐ[ℚ] ℂ) (x : K ⊗[ℚ] V) :
    ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K E V
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (E →ₗ[ℚ] V) σ (valueLineTensor K E hK τ x))
        (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ υ)) =
      if υ = τ then
        ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ x) else 0 := by
  rw [← inclusion_coeffVector K E hK,
    ← conjugate_coeffVector K E hK,
    ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients_apply_inclusion, ComplexMultiplication.HomBaseChange.CM.homBaseChange_scalarConjugate,
    valueLineTensor_apply]
  by_cases h : υ = τ <;> simp [h]

theorem valueLineTensor_complex_apply (τ υ : E →ₐ[ℚ] ℂ) (x : K ⊗[ℚ] V) :
    ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K E V (valueLineTensor K E hK τ x)
        (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E υ) =
      if υ = τ then ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V x else 0 := by
  rw [← inclusion_coeffVector K E hK,
    ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients_apply_inclusion, valueLineTensor_apply]
  by_cases h : υ = τ <;> simp [h]

theorem conjugate_line_preserves_hodge
    (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (τ : E →ₐ[ℚ] ℂ) (x : K ⊗[ℚ] V) (σ : Gal(K/ℚ))
    (htype :
      (ε.val (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ τ) = true →
        ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ x) ∈ H.holomorphic) ∧
      (ε.val (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ τ) = false →
        ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ x) ∈ H.antiholomorphic)) :
    ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K E V
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (E →ₗ[ℚ] V) σ (valueLineTensor K E hK τ x)) ∈
      ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace ε.hodgeStructure H := by
  let f := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K E V
    (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (E →ₗ[ℚ] V) σ (valueLineTensor K E hK τ x))
  have hm (b : Bool) :
      ε.subspace b ≤ (if b then H.holomorphic else H.antiholomorphic).comap f := by
    apply Submodule.span_le.mpr
    rintro y ⟨υ, hυ, rfl⟩
    obtain ⟨υ, rfl⟩ := (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbeddingEquiv K E hK σ).surjective υ
    change ε.val (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ υ) = b at hυ
    change f (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ υ)) ∈
      (if b then H.holomorphic else H.antiholomorphic)
    rw [conjugate_valueLineTensor_apply K E hK]
    by_cases h : υ = τ
    · subst υ
      simp only [ite_true]
      cases b
      · exact htype.2 hυ
      · exact htype.1 hυ
    · rw [ite_eq_right h]
      exact (if b then H.holomorphic else H.antiholomorphic).zero_mem
  exact ⟨hm true, hm false⟩

end LineMaps

theorem scalar_conjugate_one
    (K : IntermediateField ℚ ℂ)
    {V : Type*} [AddCommGroup V] [Module ℚ V] (x : K ⊗[ℚ] V) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

section IdSpan

variable (E : IntermediateField ℚ ℂ)
variable [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
variable (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
variable {V B : Type*} [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup B] [Module ℚ B]

theorem evaluate_hodge_span (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (f : ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification V)
    (hf : f ∈ ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H) :
    f (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1)) ∈ cmIdSpan E v H := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨q, hq, rfl⟩ := hf
    exact Submodule.subset_span ⟨q, hq, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul a f _ hf => exact Submodule.smul_mem _ a hf

theorem restrict_id_span
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V) (HB : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure B)
    (r : V →ₗ[ℚ] B) (hr : ComplexMultiplication.WeightOne.CM.IsHodgeMap H HB r)
    (x : ComplexMultiplication.WeightOne.CM.Complexification V) (hx : x ∈ cmIdSpan E v H) :
    r.baseChange ℂ x ∈ cmIdSpan E v HB := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    refine Submodule.subset_span ⟨r.comp f, hr.comp hf, ?_⟩
    rw [LinearMap.baseChange_comp]
    rfl
  | zero => simpa only [map_zero] using (cmIdSpan E v HB).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (cmIdSpan E v HB).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (cmIdSpan E v HB).smul_mem a hx

end IdSpan

/-- CMExtraction: holomorphic theta classes calibrate the conjugate signs,
and their active eigenspaces admit CM extraction by rational Hodge maps. -/
theorem cm_extraction_from_galois_conjugate_hodge_signs
    (E K : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    [NumberField K] [IsGalois ℚ K]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hv : v.val 1 = true)

    -- K contains the embedding values and active projector coefficients.
    (hK : ∀ τ : E →ₐ[ℚ] ℂ, τ.fieldRange ≤ K)
    (res : Gal(K/ℚ) → Gal(E/ℚ))
    (hres : ∀ σ,
      ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) =
        ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (res σ))

    -- Ambient rational Betti cohomology and its Hodge structure.
    (V : Type*) [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (hScalarDescent : ScalarTraceInput K (E →ₗ[ℚ] V))

    -- I indexes active projective parameters occurring in theta classes.
    (I Φ : Type*) [Fintype I]
    (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification V)
    (P : I → Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification V))
    (A : I → Submodule K (K ⊗[ℚ] V))
    (hprojector : ∀ i, (P i).comp (P i) = P i)
    (hcoeff : ∀ i,
      LinearMap.range (P i) = conjugateSpace K (A i) 1)
    (hHodge : ∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H)
    (htheta : ∀ φ, theta φ ∈ H.holomorphic)
    (hoccurs : ∀ i, ∃ φ, P i (theta φ) ≠ 0)
    (hdecompose : ∀ φ, ∑ i, P i (theta φ) = theta φ)

    -- The two possible orientations supplied by the slope calculation.
    (s : I → ℚ)
    (hextreme : ∀ i, s i = -3 / 2 ∨ s i = 3 / 2)
    -- ExtremeSlopes and equation (6), before calibrating the orientation.
    (hExtremeSlopes : ∀ i σ,
      let slope : ℚ :=
        1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue (v.val (res σ)) : ℚ) * s i / 3
      (slope = 1 →
        conjugateSpace K (A i) σ ≤ H.holomorphic) ∧
      (slope = 0 →
        conjugateSpace K (A i) σ ≤ H.antiholomorphic))

    -- Restriction from ambient cohomology to the chosen component.
    (B : Type*) [AddCommGroup B] [Module ℚ B]
    (HB : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure B)
    (restrict : V →ₗ[ℚ] B)
    (hrestrict : ComplexMultiplication.WeightOne.CM.IsHodgeMap H HB restrict) :

    -- Original holomorphy fixes slope 1 and hence the orientation.
    (∀ i, s i = -3 / 2) ∧

    -- Every scalar-conjugate active space has the prescribed Hodge type.
    (∀ i σ,
      (v.val (res σ) = true →
        conjugateSpace K (A i) σ ≤ H.holomorphic) ∧
      (v.val (res σ) = false →
        conjugateSpace K (A i) σ ≤ H.antiholomorphic)) ∧

    -- Algebraic Betti vectors admit maps supported on the id-line;
    -- these maps lie in the scalar span of rational Hodge maps.
    (∀ i (x : K ⊗[ℚ] V), x ∈ A i →
      ∃ f : ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification V,
        f ∈ ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H ∧
        ∀ τ : Gal(E/ℚ),
          f (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) =
            if τ = 1 then ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V x else 0) ∧

    -- Algebraic vectors span the entire complex active eigenspace.
    (∀ i, LinearMap.range (P i) ≤ cmIdSpan E v H) ∧

    -- CM extraction persists after restricting the theta classes.
    (∀ φ, restrict.baseChange ℂ (theta φ) ∈ cmIdSpan E v HB) := by
  have hres_one : res 1 = 1 := by
    apply (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).injective
    simpa only [ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding_one] using (hres 1).symm
  have hcal : ∀ i, s i = -3 / 2 := by
    intro i
    rcases hextreme i with hi | hi
    · exact hi
    · obtain ⟨φ, hne⟩ := hoccurs i
      have h10 : P i (theta φ) ∈ H.holomorphic :=
        (hHodge i).1 _ (htheta φ)
      have hanti : conjugateSpace K (A i) 1 ≤ H.antiholomorphic :=
        (hExtremeSlopes i 1).2 (by norm_num [hres_one, hv, hi, ComplexMultiplication.SignSwitch.CM.signValue])
      have hfix : P i (P i (theta φ)) = P i (theta φ) :=
        congrArg (fun T : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification V) => T (theta φ))
          (hprojector i)
      have h01 : P i (theta φ) ∈ H.antiholomorphic := by
        apply hanti
        rw [← hcoeff i]
        exact ⟨P i (theta φ), hfix⟩
      have hz : P i (theta φ) ∈ (⊥ : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V)) := by
        rw [← H.complementary.inf_eq_bot]
        exact ⟨h10, h01⟩
      exact False.elim (hne (by simpa using hz))
  have hpure : ∀ i σ,
      (v.val (res σ) = true →
        conjugateSpace K (A i) σ ≤ H.holomorphic) ∧
      (v.val (res σ) = false →
        conjugateSpace K (A i) σ ≤ H.antiholomorphic) := by
    intro i σ
    constructor
    · intro hsign
      exact (hExtremeSlopes i σ).1 (by norm_num [hsign, hcal i, ComplexMultiplication.SignSwitch.CM.signValue])
    · intro hsign
      exact (hExtremeSlopes i σ).2 (by norm_num [hsign, hcal i, ComplexMultiplication.SignSwitch.CM.signValue])
  have hline : ∀ i (x : K ⊗[ℚ] V), x ∈ A i →
      ∃ f : ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification V,
        f ∈ ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H ∧
        ∀ τ : Gal(E/ℚ),
          f (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) =
            if τ = 1 then ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V x else 0 := by
    intro i x hx
    let t := valueLineTensor K E hK (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) x
    refine ⟨ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K E V t, ?_, ?_⟩
    · apply descend_hom K (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H hScalarDescent t
      intro σ
      apply conjugate_line_preserves_hodge K E hK (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E v) H
      have hxσ : ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ x) ∈
          conjugateSpace K (A i) σ := Submodule.subset_span ⟨x, hx, rfl⟩
      constructor
      · intro hsign
        rw [hres σ, ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType_apply] at hsign
        exact (hpure i σ).1 hsign hxσ
      · intro hsign
        rw [hres σ, ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType_apply] at hsign
        exact (hpure i σ).2 hsign hxσ
    · intro τ
      change ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K E V
          (valueLineTensor K E hK (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) x)
          (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) = _
      rw [valueLineTensor_complex_apply]
      by_cases hτ : τ = 1
      · simp [hτ]
      · have hn := (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).injective.ne hτ
        simp [hτ, hn]
  have hspan : ∀ i, LinearMap.range (P i) ≤ cmIdSpan E v H := by
    intro i
    rw [hcoeff i]
    apply Submodule.span_le.mpr
    rintro y ⟨x, hx, rfl⟩
    rw [scalar_conjugate_one]
    change ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V x ∈ cmIdSpan E v H
    obtain ⟨f, hf, hvalues⟩ := hline i x hx
    have he := evaluate_hodge_span E v H f hf
    simpa only [hvalues 1, ite_true] using he
  refine ⟨hcal, hpure, hline, hspan, ?_⟩
  intro φ
  apply restrict_id_span E v H HB restrict hrestrict
  rw [← hdecompose φ]
  apply Submodule.sum_mem
  intro i _
  exact hspan i ⟨theta φ, rfl⟩

end

/-! A decomposition of the retained nonzero class contains a projector
on which that identical class is nonzero. In particular its index is inhabited. -/

open scoped BigOperators

theorem same_test_projector_occurs
    {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I]
    (P : I → Module.End ℂ V) (x : V) (hx : x ≠ 0)
    (hsum : ∑ i, P i x = x) : ∃ i, P i x ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact hx (hsum.symm.trans (Finset.sum_eq_zero (fun i _ => h i)))

theorem same_test_index_nonempty
    {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I]
    (P : I → Module.End ℂ V) (x : V) (hx : x ≠ 0)
    (hsum : ∑ i, P i x = x) : Nonempty I := by
  obtain ⟨i, _⟩ := same_test_projector_occurs P x hx hsum
  exact ⟨i⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SameTestProjector
