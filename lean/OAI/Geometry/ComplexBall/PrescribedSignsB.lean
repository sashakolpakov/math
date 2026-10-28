import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.ImaginaryElement

/-! # Prescribed Signs B -/

namespace OAI.Geometry.ComplexBall.PrescribedSignsB

noncomputable section

/-
Modeling: explicit embedding coordinates, with Hermitian forms linear in the
first variable and F = E^(c=1) represented by conjugation-fixed coefficients.
An adapted basis realizes the signature (2,1) domain as an affine chart of
negative lines; local holomorphic frames express variation. Transport to the
manuscript's tensor-product notation and the precise Riemann-form sign remain
interfaces to settle. Positivity uses psi(u, conjugate u) / i > 0.
The reserved identifier Sigma from the committed statement is renamed Place.
The explicit input hWeakApproximation is WeakApproximation specialized to E; it is used through completion
density to construct the prescribed signs. LefschetzNormalization and ArithmeticQuotient are unnecessary here:
normalization and signatures already appear as target hypotheses. RiemannProjectivity is
unnecessary for this period-subspace statement, which asserts no projectivity
of a lattice quotient. No additional substantive assumption is used, and no
committed statement stub is imported. The final axiom audit is printed below.
-/

open scoped Classical

abbrev Vec := Fin 3 → ℂ
abbrev BallChart := Fin 2 → ℂ
abbrev Ambient (Place : Type*) := Place → (Vec × Vec)

def lineVector (z : BallChart) : Vec :=
  ![z 0, z 1, 1]

/-- Conjugation swaps the two embedding coordinates. -/
def realConj {Place : Type*} (u : Ambient Place) : Ambient Place :=
  fun τ => (star (u τ).2, star (u τ).1)

/-- The local complex-bilinear pairing identifying the conjugate
embedding space with the dual of the original embedding space. -/
def localB
    {E Place : Type*} [Field E] [Algebra ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (H : Matrix (Fin 3) (Fin 3) E)
    (τ : Place) (x y : Vec) : ℂ :=
  ∑ j, ∑ k, x j * σ τ (H j k) * y k

def tracePairing
    {Place : Type*} [Fintype Place]
    (B : Place → Vec → Vec → ℂ)
    (t : Place → ℂ) (u v : Ambient Place) : ℂ :=
  ∑ τ, t τ *
    (B τ (u τ).1 (v τ).2 - B τ (v τ).1 (u τ).2)

/-- The prescribed summands. At μ, the second condition is
the annihilator of L, hence represents (Vμ / L)*. -/
def Prescribed
    {Place : Type*}
    (B : Place → Vec → Vec → ℂ)
    (μ : Place) (d : Place → Bool)
    (z : BallChart) (u : Ambient Place) : Prop :=
  ∀ τ,
    if τ = μ then
      (u τ).1 ∈ Submodule.span ℂ {lineVector z} ∧
        B τ (lineVector z) (u τ).2 = 0
    else if d τ then
      (u τ).1 = 0
    else
      (u τ).2 = 0

/-- Holomorphic variation, expressed using local holomorphic frames. -/
def HolomorphicFamily
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (O : Set BallChart) (r : ℕ)
    (P : BallChart → Submodule ℂ Y) : Prop :=
  ∀ z ∈ O, ∃ N : Set BallChart,
    IsOpen N ∧ z ∈ N ∧ N ⊆ O ∧
    ∃ e : Fin r → BallChart → Y,
      (∀ j, DifferentiableOn ℂ (e j) N) ∧
      ∀ w ∈ N,
        LinearIndependent ℂ (fun j => e j w) ∧
        Submodule.span ℂ (Set.range (fun j => e j w)) = P w

/-- Positive Lagrangian, together with its conjugate splitting
and the dimension of the homology-filtration quotient. -/
def PositivePeriod
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (r : ℕ) (ψ : Y → Y → ℂ) (κ : Y → Y)
    (P : Submodule ℂ Y) : Prop :=
  Module.finrank ℂ P = r ∧
  Module.finrank ℂ (Y ⧸ P) = r ∧
  (∀ u ∈ P, ∀ v ∈ P, ψ u v = 0) ∧
  (∀ u ∈ P, u ≠ 0 →
    (ψ u (κ u) / Complex.I).im = 0 ∧
      0 < (ψ u (κ u) / Complex.I).re) ∧
  (∀ x : Y, ∃! uv : Y × Y,
    uv.1 ∈ P ∧ uv.2 ∈ P ∧ x = uv.1 + κ uv.2)

def embeddingCoordinates
    {E Place : Type*} [Field E] [Algebra ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (x : Fin 3 → E) : Ambient Place :=
  fun τ =>
    (fun j => σ τ (x j),
     fun j => AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ) (x j))

abbrev Bilin := Vec →ₗ[ℂ] Vec →ₗ[ℂ] ℂ

def matrixB {E Place : Type*} [Field E] [Algebra ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (τ : Place) : Bilin :=
  Matrix.toBilin' (fun j k => σ τ (H j k))

lemma matrixB_apply {E Place : Type*} [Field E] [Algebra ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (τ : Place) (x y : Vec) : matrixB σ H τ x y = localB σ H τ x y := by
  exact Matrix.toBilin'_apply _ _ _

def axis (j : Fin 3) : Vec := Pi.single j 1

lemma vec_expansion (x : Vec) :
    x = x 0 • axis 0 + x 1 • axis 1 + x 2 • axis 2 := by
  ext j
  fin_cases j <;> simp [axis]

lemma linear_expansion (f : Vec →ₗ[ℂ] ℂ) (x : Vec) :
    f x = x 0 * f (axis 0) + x 1 * f (axis 1) + x 2 * f (axis 2) := by
  conv_lhs => rw [vec_expansion x]
  simp

lemma lineVector_ne_zero (z : BallChart) : lineVector z ≠ 0 := by
  intro h
  have := congrFun h 2
  simp [lineVector] at this

/-- The symmetry satisfied by the bilinear coordinate version of a Hermitian form. -/
def HermitianB (B : Bilin) : Prop :=
  ∀ x y, star (B x y) = B (star y) (star x)

lemma matrixB_hermitian {E Place : Type*} [Field E] [Algebra ℚ E]
    [NumberField E] [NumberField.IsCMField E]
    (σ : Place → E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (τ : Place) : HermitianB (matrixB σ H τ) := by
  intro x y
  rw [matrixB_apply, matrixB_apply]
  change star (∑ j, ∑ k, x j * σ τ (H j k) * y k) =
    ∑ j, ∑ k, star (y j) * σ τ (H j k) * star (x k)
  simp only [star_sum, star_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have h : star (σ τ (H k j)) = σ τ (H j k) := by
    rw [hH j k]
    exact (NumberField.IsCMField.complexEmbedding_complexConj E (σ τ).toRingHom _).symm
  rw [h]
  ring

lemma hermitian_self_real (B : Bilin) (hB : HermitianB B) (x : Vec) :
    (B x (star x)).im = 0 := by
  have h := hB x (star x)
  rw [star_star] at h
  have hi := congrArg Complex.im h
  change -(B x (star x)).im = (B x (star x)).im at hi
  linarith

lemma hermitian_swap (B : Bilin) (hB : HermitianB B) (x y : Vec) :
    B (star y) (star x) = star (B x y) := (hB x y).symm

lemma orthogonal_positive (B : Bilin) (hB : HermitianB B)
    (hp : ∀ x : Vec, x ≠ 0 → x 2 = 0 → 0 < (B x (star x)).re)
    (z : BallChart) (hz : (B (lineVector z) (star (lineVector z))).re < 0)
    (w : Vec) (hw : w ≠ 0) (ho : B (lineVector z) (star w) = 0) :
    0 < (B w (star w)).re := by
  let l := lineVector z
  let v := w - w 2 • l
  change B l (star w) = 0 at ho
  have hs : B w (star l) = 0 := by
    have h := hB l (star w)
    simpa [star_star, ho] using h.symm
  have hq : B l (star l) ≠ 0 := by
    intro h
    have : (B l (star l)).re = 0 := congrArg Complex.re h
    change (B l (star l)).re < 0 at hz
    linarith
  have hv : v ≠ 0 := by
    intro hv
    have he : w = w 2 • l := sub_eq_zero.mp hv
    have ht : w 2 = 0 := by
      rw [he, map_smul, LinearMap.smul_apply, smul_eq_mul] at hs
      exact (mul_eq_zero.mp hs).resolve_right hq
    apply hw
    rw [he, ht, zero_smul]
  have hv2 : v 2 = 0 := by
    change w 2 - w 2 * 1 = 0
    ring
  have hvp := hp v hv hv2
  have he : B v (star v) =
      B w (star w) + (w 2 * star (w 2)) * B l (star l) := by
    simp only [v, star_sub, star_smul, map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hs, ho]
    ring
  have he' := congrArg Complex.re he
  have hn : 0 ≤ Complex.normSq (w 2) := Complex.normSq_nonneg _
  have hnorm : w 2 * star (w 2) = (Complex.normSq (w 2) : ℂ) :=
    Complex.mul_conj _
  rw [hnorm] at he'
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at he'
  change (B l (star l)).re < 0 at hz
  nlinarith

lemma positivePeriod_of_positive
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [Module ℝ Y] [IsScalarTower ℝ ℂ Y] [FiniteDimensional ℂ Y]
    (r : ℕ) (ψ : Y → Y → ℂ) (κ : Y →ₗ[ℝ] Y)
    (P : Submodule ℂ Y)
    (hY : Module.finrank ℂ Y = r + r)
    (hP : Module.finrank ℂ P = r)
    (hiso : ∀ u ∈ P, ∀ v ∈ P, ψ u v = 0)
    (hpos : ∀ u ∈ P, u ≠ 0 →
      (ψ u (κ u) / Complex.I).im = 0 ∧
        0 < (ψ u (κ u) / Complex.I).re) :
    PositivePeriod r ψ κ P := by
  let : FiniteDimensional ℝ Y := FiniteDimensional.trans ℝ ℂ Y
  let : FiniteDimensional ℝ P := FiniteDimensional.trans ℝ ℂ P
  have hquot := Submodule.finrank_quotient_add_finrank P
  have hQ : Module.finrank ℂ (Y ⧸ P) = r := by omega
  refine ⟨hP, hQ, hiso, hpos, ?_⟩
  let f : P × P →ₗ[ℝ] Y :=
    (P.subtype.restrictScalars ℝ).coprod
      (κ.comp (P.subtype.restrictScalars ℝ))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨u, v⟩ h
    change (u : Y) + κ (v : Y) = 0 at h
    have hv : (v : Y) = 0 := by
      by_contra hn
      have hkv : κ (v : Y) ∈ P := by
        have he : κ (v : Y) = -(u : Y) := eq_neg_of_add_eq_zero_right h
        rw [he]
        exact P.neg_mem u.property
      have hp := (hpos v v.property hn).2
      rw [hiso v v.property _ hkv] at hp
      simp at hp
    have hu : (u : Y) = 0 := by simpa [hv] using h
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hv)
  have hdim : Module.finrank ℝ (P × P) = Module.finrank ℝ Y := by
    rw [Module.finrank_prod]
    have h₁ := Module.finrank_mul_finrank ℝ ℂ P
    have h₂ := Module.finrank_mul_finrank ℝ ℂ Y
    rw [hP] at h₁
    rw [hY] at h₂
    rw [← h₁, ← h₂]
    ring
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf
  intro x
  obtain ⟨uv, huv⟩ := hsurj x
  refine ⟨((uv.1 : Y), (uv.2 : Y)),
    ⟨uv.1.property, uv.2.property, huv.symm⟩, ?_⟩
  rintro ⟨u, v⟩ ⟨hu, hv, he⟩
  have hh : (⟨u, hu⟩, ⟨v, hv⟩) = uv := hf (he.symm.trans huv.symm)
  exact congrArg (fun p : P × P => ((p.1 : Y), (p.2 : Y))) hh

def localFrame (B : Bilin) (z : BallChart) : Vec →ₗ[ℂ] Vec × Vec :=
  (LinearMap.proj 0 : Vec →ₗ[ℂ] ℂ).smulRight (lineVector z, 0) +
  (LinearMap.proj 1 : Vec →ₗ[ℂ] ℂ).smulRight
    (0, axis 0 - (B (lineVector z) (axis 0) /
      B (lineVector z) (axis 2)) • axis 2) +
  (LinearMap.proj 2 : Vec →ₗ[ℂ] ℂ).smulRight
    (0, axis 1 - (B (lineVector z) (axis 1) /
      B (lineVector z) (axis 2)) • axis 2)

lemma localFrame_recover (B : Bilin) (z : BallChart) (v : Vec) :
    ((localFrame B z v).1 2 = v 0) ∧
    ((localFrame B z v).2 0 = v 1) ∧
    ((localFrame B z v).2 1 = v 2) := by
  simp [localFrame, lineVector, axis]

lemma localFrame_injective (B : Bilin) (z : BallChart) :
    Function.Injective (localFrame B z) := by
  intro u v h
  have hu := localFrame_recover B z u
  have hv := localFrame_recover B z v
  rw [h] at hu
  ext j
  fin_cases j
  · exact hu.1.symm.trans hv.1
  · exact hu.2.1.symm.trans hv.2.1
  · exact hu.2.2.symm.trans hv.2.2

lemma localFrame_denominator_ne_zero (B : Bilin) (hB : HermitianB B)
    (hp : ∀ x : Vec, x ≠ 0 → x 2 = 0 → 0 < (B x (star x)).re)
    (hn : (B (axis 2) (axis 2)).re < 0)
    (z : BallChart) (hz : (B (lineVector z) (star (lineVector z))).re < 0) :
    B (lineVector z) (axis 2) ≠ 0 := by
  intro h
  have ha : axis 2 ≠ 0 := by
    intro he
    have := congrFun he 2
    simp [axis] at this
  have hstar : star (axis 2) = axis 2 := by simp [axis]
  have hp' := orthogonal_positive B hB hp z hz (axis 2) ha (by rwa [hstar])
  rw [hstar] at hp'
  linarith

lemma localFrame_mem (B : Bilin) (z : BallChart)
    (hq : B (lineVector z) (axis 2) ≠ 0) (v : Vec) :
    (localFrame B z v).1 ∈ Submodule.span ℂ {lineVector z} ∧
      B (lineVector z) (localFrame B z v).2 = 0 := by
  constructor
  · apply Submodule.mem_span_singleton.mpr
    exact ⟨v 0, by simp [localFrame]⟩
  · have h₀ : B (lineVector z)
        (axis 0 - (B (lineVector z) (axis 0) /
          B (lineVector z) (axis 2)) • axis 2) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hq, sub_self]
    have h₁ : B (lineVector z)
        (axis 1 - (B (lineVector z) (axis 1) /
          B (lineVector z) (axis 2)) • axis 2) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hq, sub_self]
    simp [localFrame, h₀, h₁]

lemma localFrame_range (B : Bilin) (z : BallChart)
    (hq : B (lineVector z) (axis 2) ≠ 0) (u : Vec × Vec) :
    u ∈ LinearMap.range (localFrame B z) ↔
      u.1 ∈ Submodule.span ℂ {lineVector z} ∧ B (lineVector z) u.2 = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact localFrame_mem B z hq v
  · rintro ⟨hx, hy⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
    let v : Vec := ![t, u.2 0, u.2 1]
    refine ⟨v, Prod.ext ?_ ?_⟩
    · simpa [localFrame, v] using ht
    · have hmem := (localFrame_mem B z hq v).2
      have hcoords := localFrame_recover B z v
      have h₀ : (localFrame B z v).2 0 = u.2 0 := hcoords.2.1
      have h₁ : (localFrame B z v).2 1 = u.2 1 := hcoords.2.2
      rw [linear_expansion] at hmem hy
      rw [h₀, h₁] at hmem
      have h₂ : (localFrame B z v).2 2 = u.2 2 := by
        apply mul_right_cancel₀ hq
        linear_combination hmem - hy
      ext j
      fin_cases j
      · exact h₀
      · exact h₁
      · exact h₂

lemma lineVector_differentiable : Differentiable ℂ lineVector := by
  apply differentiable_pi.mpr
  intro j
  fin_cases j
  · change Differentiable ℂ (fun z : BallChart => z 0)
    fun_prop
  · change Differentiable ℂ (fun z : BallChart => z 1)
    fun_prop
  · change Differentiable ℂ (fun _ : BallChart => (1 : ℂ))
    fun_prop

lemma coefficient_differentiable (B : Bilin) (j : Fin 3) :
    Differentiable ℂ (fun z => B (lineVector z) (axis j)) :=
  (B.flip (axis j)).toContinuousLinearMap.differentiable.comp lineVector_differentiable

lemma negative_domain_isOpen (B : Bilin) :
    IsOpen {z : BallChart | (B (lineVector z) (star (lineVector z))).re < 0} := by
  apply isOpen_lt _ continuous_const
  apply Complex.continuous_re.comp
  have he : (fun z => B (lineVector z) (star (lineVector z))) =
      (fun z => star (lineVector z) 0 * B (lineVector z) (axis 0) +
        star (lineVector z) 1 * B (lineVector z) (axis 1) +
        star (lineVector z) 2 * B (lineVector z) (axis 2)) :=
    funext (fun z => linear_expansion (B (lineVector z)) (star (lineVector z)))
  rw [he]
  have hq (j : Fin 3) := (coefficient_differentiable B j).continuous
  have hl (j : Fin 3) : Continuous (fun z => star (lineVector z) j) :=
    (continuous_apply j).comp lineVector_differentiable.continuous.star
  exact (((hl 0).mul (hq 0)).add ((hl 1).mul (hq 1))).add ((hl 2).mul (hq 2))

lemma localFrame_differentiable (B : Bilin) (O : Set BallChart)
    (hq : ∀ z ∈ O, B (lineVector z) (axis 2) ≠ 0) (v : Vec) :
    DifferentiableOn ℂ (fun z => localFrame B z v) O := by
  have hl := lineVector_differentiable.differentiableOn (s := O)
  have hd (j : Fin 3) : DifferentiableOn ℂ
      (fun z => B (lineVector z) (axis j) / B (lineVector z) (axis 2)) O := by
    simp only [div_eq_mul_inv]
    apply DifferentiableOn.mul
    · exact (coefficient_differentiable B j).differentiableOn
    · exact (coefficient_differentiable B 2).differentiableOn.inv hq
  change DifferentiableOn ℂ (fun z =>
    v 0 • (lineVector z, (0 : Vec)) +
      v 1 • ((0 : Vec), axis 0 -
        (B (lineVector z) (axis 0) / B (lineVector z) (axis 2)) • axis 2) +
      v 2 • ((0 : Vec), axis 1 -
        (B (lineVector z) (axis 1) / B (lineVector z) (axis 2)) • axis 2)) O
  fun_prop

lemma holomorphicFamily_range
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (O : Set BallChart) (hO : IsOpen O)
    (f : BallChart → X →ₗ[ℂ] Y)
    (hinj : ∀ z ∈ O, Function.Injective (f z))
    (hhol : ∀ x, DifferentiableOn ℂ (fun z => f z x) O) :
    HolomorphicFamily O (Module.finrank ℂ X) (fun z => LinearMap.range (f z)) := by
  intro z hz
  let b := Module.finBasis ℂ X
  refine ⟨O, hO, hz, Set.Subset.rfl, (fun j w => f w (b j)), ?_, ?_⟩
  · intro j
    exact hhol (b j)
  · intro w hw
    refine ⟨b.linearIndependent.map' (f w) (LinearMap.ker_eq_bot.mpr (hinj w hw)), ?_⟩
    change Submodule.span ℂ (Set.range ((f w) ∘ b)) = LinearMap.range (f w)
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq]
    exact Submodule.map_top _

def placeFrame {Place : Type*} (B : Place → Bilin) (μ : Place)
    (d : Place → Bool) (z : BallChart) (τ : Place) : Vec →ₗ[ℂ] Vec × Vec :=
  if τ = μ then localFrame (B μ) z
  else if d τ then LinearMap.inr ℂ Vec Vec else LinearMap.inl ℂ Vec Vec

def globalFrame {Place : Type*} (B : Place → Bilin) (μ : Place)
    (d : Place → Bool) (z : BallChart) : (Place → Vec) →ₗ[ℂ] Ambient Place :=
  LinearMap.pi (fun τ => (placeFrame B μ d z τ).comp (LinearMap.proj τ))

lemma placeFrame_injective {Place : Type*} (B : Place → Bilin) (μ : Place)
    (d : Place → Bool) (z : BallChart) (τ : Place) :
    Function.Injective (placeFrame B μ d z τ) := by
  unfold placeFrame
  split_ifs
  · exact localFrame_injective _ _
  · exact LinearMap.inr_injective
  · exact LinearMap.inl_injective

lemma globalFrame_injective {Place : Type*} (B : Place → Bilin) (μ : Place)
    (d : Place → Bool) (z : BallChart) : Function.Injective (globalFrame B μ d z) := by
  intro u v h
  funext τ
  exact placeFrame_injective B μ d z τ (congrFun h τ)

lemma globalFrame_range {Place : Type*} (B : Place → Bilin) (μ : Place)
    (d : Place → Bool) (z : BallChart)
    (hq : B μ (lineVector z) (axis 2) ≠ 0) (u : Ambient Place) :
    u ∈ LinearMap.range (globalFrame B μ d z) ↔
      Prescribed (fun τ x y => B τ x y) μ d z u := by
  have hlocal (τ : Place) : u τ ∈ LinearMap.range (placeFrame B μ d z τ) ↔
      if τ = μ then
        (u τ).1 ∈ Submodule.span ℂ {lineVector z} ∧ B τ (lineVector z) (u τ).2 = 0
      else if d τ then (u τ).1 = 0 else (u τ).2 = 0 := by
    unfold placeFrame
    split_ifs with he hd
    · subst τ
      exact localFrame_range _ _ hq _
    · simp only [LinearMap.mem_range, LinearMap.inr_apply]
      constructor
      · rintro ⟨v, hv⟩
        exact (congrArg Prod.fst hv).symm
      · intro hv
        exact ⟨(u τ).2, Prod.ext hv.symm rfl⟩
    · simp only [LinearMap.mem_range, LinearMap.inl_apply]
      constructor
      · rintro ⟨v, hv⟩
        exact (congrArg Prod.snd hv).symm
      · intro hv
        exact ⟨(u τ).1, Prod.ext rfl hv.symm⟩
  constructor
  · rintro ⟨v, rfl⟩ τ
    exact (hlocal τ).mp ⟨v τ, rfl⟩
  · intro hu
    have hv : ∀ τ, ∃ v, placeFrame B μ d z τ v = u τ :=
      fun τ => (hlocal τ).mpr (hu τ)
    choose v hv using hv
    exact ⟨v, funext hv⟩

lemma globalFrame_differentiable {Place : Type*} [Fintype Place]
    (B : Place → Bilin) (μ : Place) (d : Place → Bool)
    (O : Set BallChart) (hq : ∀ z ∈ O, B μ (lineVector z) (axis 2) ≠ 0)
    (v : Place → Vec) : DifferentiableOn ℂ (fun z => globalFrame B μ d z v) O := by
  apply differentiableOn_pi.mpr
  intro τ
  change DifferentiableOn ℂ (fun z => placeFrame B μ d z τ (v τ)) O
  unfold placeFrame
  split_ifs
  · exact localFrame_differentiable _ _ hq _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

universe u

/-- WeakApproximation's proposition, specialized to the coefficient field and arbitrary
finite index types in the same universe. It is an input, not a statement stub. -/
def WeakApproximationInput (E : Type u) [Field E] [NumberField E] : Prop :=
  ∀ {ι : Type u} [Finite ι] (v : ι → AbsoluteValue E ℝ),
    (∀ i, (v i).IsNontrivial) →
    (Pairwise fun i j => ¬ (v i).IsEquiv (v j)) →
    DenseRange (fun x : E => fun i : ι => (x : (v i).Completion))

lemma weakApproximation_withAbs (E : Type u) [Field E] [NumberField E]
    (hWeakApproximation : WeakApproximationInput E) :
    DenseRange (algebraMap E ((v : NumberField.InfinitePlace E) → WithAbs v.1)) := by
  let f := algebraMap E ((v : NumberField.InfinitePlace E) → WithAbs v.1)
  let g : ((v : NumberField.InfinitePlace E) → WithAbs v.1) →
      ((v : NumberField.InfinitePlace E) → v.1.Completion) :=
    fun x v => (x v : v.1.Completion)
  have hg : Topology.IsInducing g :=
    Topology.IsInducing.piMap (fun v =>
      (UniformSpace.Completion.isUniformInducing_coe (WithAbs v.1)).isInducing)
  have hd : DenseRange (g ∘ f) := hWeakApproximation (fun v : NumberField.InfinitePlace E => v.1)
    (fun v => v.isNontrivial)
    (fun v w h => (NumberField.InfinitePlace.eq_iff_isEquiv (K := E)).not.mp h)
  apply hg.dense_iff.mpr
  intro x
  change g x ∈ closure (g '' Set.range f)
  rw [← Set.range_comp]
  exact hd (g x)

lemma imaginaryElement_of_weakApproximation
    {E : Type u} [Field E] [Algebra ℚ E] [NumberField E]
    [NumberField.IsCMField E]
    (hWeakApproximation : WeakApproximationInput E) (ε : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ ξ : E, NumberField.IsCMField.complexConj E ξ = -ξ ∧
      ∀ σ : E →ₐ[ℚ] ℂ, ε.val σ = true → 0 < (σ ξ).im := by
  let O : Set ((v : NumberField.InfinitePlace E) → WithAbs v.1) :=
    {x | ∀ v, 0 < (ε.placeEmbedding v (WithAbs.equiv v.1 (x v))).im}
  have ho : IsOpen O := by
    dsimp only [O]
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro v
    exact isOpen_lt continuous_const
      (Complex.continuous_im.comp
        ((ε.placeEmbedding_isometry v).continuous.comp (continuous_apply v)))
  have hn : O.Nonempty := by
    choose a ha using (fun v : NumberField.InfinitePlace E =>
      AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.exists_positive_im (ε.placeEmbedding v))
    refine ⟨fun v => (WithAbs.equiv v.1).symm (a v), ?_⟩
    intro v
    simpa only [RingEquiv.apply_symm_apply] using ha v
  obtain ⟨x, hx⟩ := (weakApproximation_withAbs E hWeakApproximation).exists_mem_open ho hn
  have hp (σ : E →ₐ[ℚ] ℂ) (hσ : ε.val σ = true) : 0 < (σ x).im := by
    have hv := hx (NumberField.InfinitePlace.mk σ.toRingHom)
    rw [ε.placeEmbedding_mk σ hσ] at hv
    exact hv
  refine ⟨x - NumberField.IsCMField.complexConj E x, ?_, ?_⟩
  · simp only [map_sub, NumberField.IsCMField.complexConj_apply_apply, neg_sub]
  · intro σ hσ
    have hp' := hp σ hσ
    have hc : σ (NumberField.IsCMField.complexConj E x) = star (σ x) :=
      NumberField.IsCMField.complexEmbedding_complexConj E σ.toRingHom x
    rw [map_sub, Complex.sub_im, hc]
    change 0 < (σ x).im - -(σ x).im
    linarith

lemma scalar_with_prescribed_signs
    {E : Type u} {Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]
    [NumberField.IsCMField E] [Fintype Place]
    (hWeakApproximation : WeakApproximationInput E)
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (τ₀ : Place) (δ : E) (hδ : δ ≠ 0)
    (hδc : NumberField.IsCMField.complexConj E δ = -δ)
    (s : Place → Bool) :
    ∃ a : E, a ≠ 0 ∧ NumberField.IsCMField.complexConj E a = a ∧
      ∀ τ, if s τ then 0 < (σ τ (δ * a)).im else (σ τ (δ * a)).im < 0 := by
  let e : Place × Bool ≃ (E →ₐ[ℚ] ℂ) := Equiv.ofBijective _ hσ
  have he (p : Place × Bool) : AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (e p) = e (p.1, !p.2) := by
    rcases p with ⟨τ, b⟩
    cases b <;> simp [e, AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
  let ε : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E :=
    ⟨fun ρ => if (e.symm ρ).2 then !(s (e.symm ρ).1) else s (e.symm ρ).1,
      fun ρ => by
        have hh : e.symm (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding ρ) = ((e.symm ρ).1, !(e.symm ρ).2) := by
          apply e.injective
          rw [Equiv.apply_symm_apply, ← he, Equiv.apply_symm_apply]
        dsimp only
        rw [hh]
        cases hb : (e.symm ρ).2 <;> simp⟩
  have hε (τ : Place) : ε.val (σ τ) = s τ := by
    change (if (e.symm (e (τ, false))).2 then
      !(s (e.symm (e (τ, false))).1) else s (e.symm (e (τ, false))).1) = s τ
    simp
  obtain ⟨ξ, hξc, hξ⟩ := imaginaryElement_of_weakApproximation hWeakApproximation ε
  have hsign (τ : Place) : if s τ then 0 < (σ τ ξ).im else (σ τ ξ).im < 0 := by
    cases hs : s τ
    · have hp := hξ (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ)) (by rw [ε.property, hε, hs]; rfl)
      change 0 < -((σ τ) ξ).im at hp
      exact neg_pos.mp hp
    · simpa only [hs, ↓reduceIte] using hξ (σ τ) (by rw [hε, hs])
  have hξ0 : ξ ≠ 0 := by
    intro hz
    have ht := hsign τ₀
    rw [hz, map_zero] at ht
    split_ifs at ht <;> simp at ht
  refine ⟨ξ / δ, div_ne_zero hξ0 hδ, ?_, ?_⟩
  · simp only [map_div₀, hξc, hδc, neg_div_neg_eq]
  · intro τ
    have heq : δ * (ξ / δ) = ξ := by field_simp
    rw [heq]
    exact hsign τ

def PositiveB (B : Bilin) : Prop := ∀ x : Vec, x ≠ 0 → 0 < (B x (star x)).re
def NegativeB (B : Bilin) : Prop := ∀ x : Vec, x ≠ 0 → (B x (star x)).re < 0

def metricValue (B : Bilin) (u : Vec × Vec) : ℂ :=
  B u.1 (star u.1) - B (star u.2) u.2

lemma metricValue_real (B : Bilin) (hB : HermitianB B) (u : Vec × Vec) :
    (metricValue B u).im = 0 := by
  have h := hermitian_self_real B hB (star u.2)
  rw [star_star] at h
  simp only [metricValue, Complex.sub_im, hermitian_self_real B hB, h, sub_self]

lemma self_smul (B : Bilin) (t : ℂ) (x : Vec) :
    B (t • x) (star (t • x)) = (Complex.normSq t : ℂ) * B x (star x) := by
  have hn : t * star t = (Complex.normSq t : ℂ) := Complex.mul_conj _
  simp only [star_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_comm (star t) t, hn]

lemma span_negative (B : Bilin) (z : BallChart)
    (hz : (B (lineVector z) (star (lineVector z))).re < 0)
    (x : Vec) (hx : x ∈ Submodule.span ℂ {lineVector z}) (hne : x ≠ 0) :
    (B x (star x)).re < 0 := by
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have ht : t ≠ 0 := by intro ht; simp [ht] at hne
  rw [self_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr ht) hz

lemma distinguished_metric_negative (B : Bilin) (hB : HermitianB B)
    (hp : ∀ x : Vec, x ≠ 0 → x 2 = 0 → 0 < (B x (star x)).re)
    (z : BallChart) (hz : (B (lineVector z) (star (lineVector z))).re < 0)
    (u : Vec × Vec)
    (hu : u.1 ∈ Submodule.span ℂ {lineVector z} ∧ B (lineVector z) u.2 = 0)
    (hne : u ≠ 0) : (metricValue B u).re < 0 := by
  have hx : (B u.1 (star u.1)).re ≤ 0 := by
    by_cases hx : u.1 = 0
    · simp [hx]
    · exact (span_negative B z hz u.1 hu.1 hx).le
  by_cases hy : u.2 = 0
  · have hnx : u.1 ≠ 0 := by
      intro hx
      apply hne
      exact Prod.ext hx hy
    simpa [metricValue, hy] using span_negative B z hz u.1 hu.1 hnx
  · have hny : star u.2 ≠ 0 := star_ne_zero.mpr hy
    have hp' := orthogonal_positive B hB hp z hz (star u.2) hny (by simpa using hu.2)
    rw [star_star] at hp'
    simp only [metricValue, Complex.sub_re]
    linarith

lemma compact_metric_sign (B : Bilin) (b d : Bool)
    (hB : if b then PositiveB B else NegativeB B)
    (u : Vec × Vec) (hu : if d then u.1 = 0 else u.2 = 0) (hne : u ≠ 0) :
    if (if d then !b else b) then 0 < (metricValue B u).re
      else (metricValue B u).re < 0 := by
  rcases u with ⟨x, y⟩
  cases d
  · change y = 0 at hu
    subst y
    have hx : x ≠ 0 := by intro hx; simp [hx] at hne
    cases b <;> simpa [metricValue] using hB x hx
  · change x = 0 at hu
    subst x
    have hy : star y ≠ 0 := by
      apply star_ne_zero.mpr
      intro hy
      simp [hy] at hne
    cases b <;> simpa [metricValue, star_star] using hB (star y) hy

lemma imaginary_weight (t q : ℂ) (ht : t.re = 0) (hq : q.im = 0) :
    (t * q / Complex.I).im = 0 ∧ (t * q / Complex.I).re = t.im * q.re := by
  simp [Complex.mul_re, Complex.mul_im, ht, hq]

def realConjLinearMap (Place : Type*) : Ambient Place →ₗ[ℝ] Ambient Place where
  toFun := realConj
  map_add' u v := by ext τ <;> simp [realConj, star_add]
  map_smul' t u := by ext τ <;> simp [realConj, star_smul]

lemma place_isotropic {Place : Type*} (B : Place → Bilin) (μ : Place)
    (d : Place → Bool) (z : BallChart)
    (hq : B μ (lineVector z) (axis 2) ≠ 0)
    (τ : Place) (u v : Vec × Vec)
    (hu : u ∈ LinearMap.range (placeFrame B μ d z τ))
    (hv : v ∈ LinearMap.range (placeFrame B μ d z τ)) :
    B τ u.1 v.2 - B τ v.1 u.2 = 0 := by
  unfold placeFrame at hu hv
  split_ifs at hu hv with he hd
  · subst τ
    obtain ⟨hu₁, hu₂⟩ := (localFrame_range _ _ hq _).mp hu
    obtain ⟨hv₁, hv₂⟩ := (localFrame_range _ _ hq _).mp hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu₁
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv₁
    rw [← ha, ← hb, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      hu₂, hv₂, smul_zero, smul_zero, sub_self]
  · obtain ⟨u, rfl⟩ := hu
    obtain ⟨v, rfl⟩ := hv
    simp
  · obtain ⟨u, rfl⟩ := hu
    obtain ⟨v, rfl⟩ := hv
    simp

lemma globalFrame_positivePeriod {Place : Type*} [Fintype Place]
    (B : Place → Bilin) (hB : ∀ τ, HermitianB (B τ))
    (μ : Place) (d : Place → Bool) (z : BallChart)
    (hq : B μ (lineVector z) (axis 2) ≠ 0)
    (t : Place → ℂ) (ht : ∀ τ, (t τ).re = 0)
    (hp : ∀ τ u, u ∈ LinearMap.range (placeFrame B μ d z τ) → u ≠ 0 →
      0 < (t τ * metricValue (B τ) u / Complex.I).re) :
    PositivePeriod (3 * Fintype.card Place)
      (tracePairing (fun τ x y => B τ x y) t) realConj
      (LinearMap.range (globalFrame B μ d z)) := by
  have hY : Module.finrank ℂ (Ambient Place) =
      3 * Fintype.card Place + 3 * Fintype.card Place := by
    simp [Ambient, Vec, Module.finrank_pi_fintype, Module.finrank_prod]
    omega
  have hP : Module.finrank ℂ (LinearMap.range (globalFrame B μ d z)) =
      3 * Fintype.card Place := by
    rw [LinearMap.finrank_range_of_inj (globalFrame_injective B μ d z)]
    simp [Vec, Module.finrank_pi_fintype, Nat.mul_comm]
  apply positivePeriod_of_positive _ _ (realConjLinearMap Place) _ hY hP
  · rintro u ⟨a, rfl⟩ v ⟨b, rfl⟩
    apply Finset.sum_eq_zero
    intro τ _
    change t τ * (B τ (placeFrame B μ d z τ (a τ)).1 (placeFrame B μ d z τ (b τ)).2 -
      B τ (placeFrame B μ d z τ (b τ)).1 (placeFrame B μ d z τ (a τ)).2) = 0
    rw [place_isotropic B μ d z hq τ _ _ ⟨a τ, rfl⟩ ⟨b τ, rfl⟩, mul_zero]
  · intro u hu hne
    have huτ (τ : Place) : u τ ∈ LinearMap.range (placeFrame B μ d z τ) := by
      obtain ⟨a, rfl⟩ := hu
      exact ⟨a τ, rfl⟩
    have heq : tracePairing (fun τ x y => B τ x y) t u (realConjLinearMap Place u) /
        Complex.I = ∑ τ, t τ * metricValue (B τ) (u τ) / Complex.I := by
      simp only [tracePairing, realConjLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
        realConj, metricValue, Finset.sum_div]
    rw [heq]
    constructor
    · rw [Complex.im_sum]
      exact Finset.sum_eq_zero (fun τ _ =>
        (imaginary_weight (t τ) _ (ht τ) (metricValue_real _ (hB τ) _)).1)
    · rw [Complex.re_sum]
      have hn (τ : Place) : 0 ≤ (t τ * metricValue (B τ) (u τ) / Complex.I).re := by
        by_cases hz : u τ = 0
        · simp [hz, metricValue]
        · exact (hp τ (u τ) (huτ τ) hz).le
      apply (Finset.sum_pos_iff_of_nonneg (fun τ _ => hn τ)).mpr
      have hex : ∃ τ, u τ ≠ 0 := by
        by_contra! h
        exact hne (funext h)
      obtain ⟨τ, hτ⟩ := hex
      exact ⟨τ, Finset.mem_univ τ, hp τ (u τ) (huτ τ) hτ⟩

def prodSubmoduleEquiv {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (P Q : Submodule ℂ Y) : P.prod Q ≃ₗ[ℂ] P × Q where
  toFun x := (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
  invFun x := ⟨(x.1.val, x.2.val), ⟨x.1.property, x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma period_self_nonnegative {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [Module ℝ Y] (r : ℕ) (ψ : Y → Y → ℂ) (κ : Y →ₗ[ℝ] Y)
    (P : Submodule ℂ Y) (h : PositivePeriod r ψ κ P) (u : Y) (hu : u ∈ P) :
    (ψ u (κ u) / Complex.I).im = 0 ∧ 0 ≤ (ψ u (κ u) / Complex.I).re := by
  by_cases hn : u = 0
  · subst u
    have hz : ψ 0 (κ 0) = 0 := by simpa using h.2.2.1 0 P.zero_mem 0 P.zero_mem
    rw [hz]
    simp
  · exact ⟨(h.2.2.2.1 u hu hn).1, (h.2.2.2.1 u hu hn).2.le⟩

lemma positivePeriod_prod {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [Module ℝ Y] [IsScalarTower ℝ ℂ Y] [FiniteDimensional ℂ Y]
    (r : ℕ) (ψ₀ ψ₁ : Y → Y → ℂ) (κ₀ κ₁ : Y →ₗ[ℝ] Y)
    (P Q : Submodule ℂ Y) (hY : Module.finrank ℂ Y = r + r)
    (hP : PositivePeriod r ψ₀ κ₀ P) (hQ : PositivePeriod r ψ₁ κ₁ Q) :
    PositivePeriod (r + r) (fun u v => ψ₀ u.1 v.1 + ψ₁ u.2 v.2)
      (fun u => (κ₀ u.1, κ₁ u.2)) (P.prod Q) := by
  have hYY : Module.finrank ℂ (Y × Y) = (r + r) + (r + r) := by
    rw [Module.finrank_prod, hY]
  have hPQ : Module.finrank ℂ (P.prod Q) = r + r := by
    rw [(prodSubmoduleEquiv P Q).finrank_eq, Module.finrank_prod, hP.1, hQ.1]
  apply positivePeriod_of_positive _ _ (κ₀.prodMap κ₁) _ hYY hPQ
  · intro u hu v hv
    rw [hP.2.2.1 _ hu.1 _ hv.1, hQ.2.2.1 _ hu.2 _ hv.2, add_zero]
  · intro u hu hn
    have hp := period_self_nonnegative r ψ₀ κ₀ P hP u.1 hu.1
    have hq := period_self_nonnegative r ψ₁ κ₁ Q hQ u.2 hu.2
    change ((ψ₀ u.1 (κ₀ u.1) + ψ₁ u.2 (κ₁ u.2)) / Complex.I).im = 0 ∧
      0 < ((ψ₀ u.1 (κ₀ u.1) + ψ₁ u.2 (κ₁ u.2)) / Complex.I).re
    rw [add_div, Complex.add_im, Complex.add_re, hp.1, hq.1, zero_add]
    refine ⟨rfl, ?_⟩
    by_cases h₀ : u.1 = 0
    · have h₁ : u.2 ≠ 0 := by intro h₁; exact hn (Prod.ext h₀ h₁)
      exact add_pos_of_nonneg_of_pos hp.2 (hQ.2.2.2.1 _ hu.2 h₁).2
    · exact add_pos_of_pos_of_nonneg (hP.2.2.2.1 _ hu.1 h₀).2 hq.2

lemma coefficient_conjugate {E : Type*} [Field E] [Algebra ℚ E]
    [NumberField E] [NumberField.IsCMField E]
    (σ : E →ₐ[ℚ] ℂ) (δ a : E)
    (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a) :
    star (σ (δ * a)) = -σ (δ * a) := by
  have h := NumberField.IsCMField.complexEmbedding_complexConj E σ.toRingHom (δ * a)
  change σ (NumberField.IsCMField.complexConj E (δ * a)) = star (σ (δ * a)) at h
  rw [← h]
  simp only [map_mul, hδ, ha, map_neg, neg_mul]

lemma coefficient_real_zero {E : Type*} [Field E] [Algebra ℚ E]
    [NumberField E] [NumberField.IsCMField E]
    (σ : E →ₐ[ℚ] ℂ) (δ a : E)
    (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a) : (σ (δ * a)).re = 0 := by
  have h := congrArg Complex.re (coefficient_conjugate σ δ a hδ ha)
  change (σ (δ * a)).re = -(σ (δ * a)).re at h
  linarith

lemma tracePairing_rational {E Place : Type*} [Field E] [Algebra ℚ E]
    [NumberField E] [NumberField.IsCMField E] [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (x y : Fin 3 → E) :
    tracePairing (localB σ H) (fun τ => σ τ (δ * a))
      (embeddingCoordinates σ x) (embeddingCoordinates σ y) =
      ((Algebra.trace ℚ E (δ * a *
        (∑ j, ∑ k, x j * H j k * NumberField.IsCMField.complexConj E (y k)))) : ℂ) := by
  let q := δ * a * (∑ j, ∑ k, x j * H j k * NumberField.IsCMField.complexConj E (y k))
  let e : Place × Bool ≃ (E →ₐ[ℚ] ℂ) := Equiv.ofBijective _ hσ
  have hm (τ : Place) : σ τ q = σ τ (δ * a) *
      matrixB σ H τ (fun j => σ τ (x j)) (fun j => star (σ τ (y j))) := by
    rw [matrixB_apply]
    have hc (v : E) : σ τ (NumberField.IsCMField.complexConj E v) = star (σ τ v) :=
      NumberField.IsCMField.complexEmbedding_complexConj E (σ τ).toRingHom v
    simp only [q, localB, map_mul, map_sum, hc]
  change _ = algebraMap ℚ ℂ (Algebra.trace ℚ E q)
  rw [trace_eq_sum_embeddings ℂ, ← Equiv.sum_comp e (fun ρ => ρ q)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Fintype.sum_bool]
  change σ τ (δ * a) *
      (localB σ H τ (fun j => σ τ (x j)) (fun j => star (σ τ (y j))) -
        localB σ H τ (fun j => σ τ (y j)) (fun j => star (σ τ (x j)))) =
    star (σ τ q) + σ τ q
  rw [hm, star_mul, coefficient_conjugate _ _ _ hδ ha,
    matrixB_hermitian σ H hH τ]
  have hy : star (fun j => star (σ τ (y j))) = (fun j => σ τ (y j)) := by
    funext j
    exact star_star _
  rw [hy]
  simp only [matrixB_apply]
  have hx : star (fun j => σ τ (x j)) = (fun j => star (σ τ (x j))) := rfl
  rw [hx]
  ring

def wantedSign {Place : Type*} (B : Place → Bilin) (μ : Place)
    (d : Place → Bool) (τ : Place) : Bool :=
  if τ = μ then false else
    if d τ then !(decide (PositiveB (B τ))) else decide (PositiveB (B τ))

lemma wantedSign_positive {Place : Type*}
    (B : Place → Bilin) (hB : ∀ τ, HermitianB (B τ)) (μ : Place)
    (hp : ∀ x : Vec, x ≠ 0 → x 2 = 0 → 0 < (B μ x (star x)).re)
    (hc : ∀ τ, τ ≠ μ → PositiveB (B τ) ∨ NegativeB (B τ))
    (d : Place → Bool) (z : BallChart)
    (hz : (B μ (lineVector z) (star (lineVector z))).re < 0)
    (hq : B μ (lineVector z) (axis 2) ≠ 0)
    (τ : Place) (t : ℂ) (ht : t.re = 0)
    (hs : if wantedSign B μ d τ then 0 < t.im else t.im < 0)
    (u : Vec × Vec) (hu : u ∈ LinearMap.range (placeFrame B μ d z τ)) (hne : u ≠ 0) :
    0 < (t * metricValue (B τ) u / Complex.I).re := by
  rw [(imaginary_weight t _ ht (metricValue_real _ (hB τ) _)).2]
  by_cases he : τ = μ
  · subst τ
    have hs' : t.im < 0 := by simpa [wantedSign] using hs
    have hu' : u ∈ LinearMap.range (localFrame (B μ) z) := by
      simpa [placeFrame] using hu
    exact mul_pos_of_neg_of_neg hs'
      (distinguished_metric_negative (B μ) (hB μ) hp z hz u
        ((localFrame_range _ _ hq _).mp hu') hne)
  · have hf : if decide (PositiveB (B τ)) then PositiveB (B τ) else NegativeB (B τ) := by
      by_cases hb : PositiveB (B τ)
      · simp [hb]
      · simpa [hb] using (hc τ he).resolve_left hb
    have hu' : if d τ then u.1 = 0 else u.2 = 0 := by
      unfold placeFrame at hu
      rw [ite_eq_right he] at hu
      cases hd : d τ
      · simp only [hd, Bool.false_eq_true, ↓reduceIte] at hu ⊢
        obtain ⟨v, rfl⟩ := hu
        rfl
      · simp only [hd, ↓reduceIte] at hu ⊢
        obtain ⟨v, rfl⟩ := hu
        rfl
    have hm := compact_metric_sign (B τ) (decide (PositiveB (B τ))) (d τ) hf u hu' hne
    simp only [wantedSign, ite_eq_right he] at hs
    split_ifs at hs hm <;>
      first | exact mul_pos hs hm | exact mul_pos_of_neg_of_neg hs hm

/-- PrescribedSigns: prescribed compact-place signs admit Hermitian line
forms and holomorphic positive Lagrangians, individually and
for their orthogonal direct sum. -/
theorem lagrangians_with_prescribed_compact_place_signs
    {E : Type u} {Place : Type*}
    [Field E] [Algebra ℚ E] [NumberField E]
    [IsGalois ℚ E] [NumberField.IsCMField E]
    [Fintype Place]
    (hWeakApproximation : WeakApproximationInput E)
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool =>
        if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (μ : Place)
    (δ : E) (hδ : δ ≠ 0)
    (hδc : NumberField.IsCMField.complexConj E δ = -δ)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hHermitian : ∀ j k,
      H j k = NumberField.IsCMField.complexConj E (H k j))
    -- An adapted basis at μ: the first two coordinates are
    -- positive, and the final basis vector is negative.
    (hμpos : ∀ x : Vec, x ≠ 0 → x 2 = 0 →
      0 < (localB σ H μ x (star x)).re)
    (hμneg :
      (localB σ H μ ![0, 0, 1] ![0, 0, 1]).re < 0)
    (hcompact : ∀ τ, τ ≠ μ →
      (∀ x : Vec, x ≠ 0 →
        0 < (localB σ H τ x (star x)).re) ∨
      (∀ x : Vec, x ≠ 0 →
        (localB σ H τ x (star x)).re < 0))
    (d : Fin 2 → Place → Bool) :
    let B := localB σ H
    let O : Set BallChart :=
      {z | (B μ (lineVector z) (star (lineVector z))).re < 0}
    let r := 3 * Fintype.card Place
    ∃ (a : Fin 2 → E)
      (ℱ : Fin 2 → BallChart → Submodule ℂ (Ambient Place)),
      let ψ : Fin 2 → Ambient Place → Ambient Place → ℂ :=
        fun i => tracePairing B (fun τ => σ τ (δ * a i))
      -- Wᵢ = E, with hᵢ(s,t) = aᵢ s c(t).
      (∀ i, a i ≠ 0 ∧
        NumberField.IsCMField.complexConj E (a i) = a i ∧
        (σ μ (δ * a i)).im < 0) ∧
      (∀ i, HolomorphicFamily O r (ℱ i)) ∧
      (∀ i z, z ∈ O →
        (∀ u, u ∈ ℱ i z ↔ Prescribed B μ (d i) z u) ∧
        PositivePeriod r (ψ i) realConj (ℱ i z)) ∧
      -- W = W₁ ⊥ W₂.
      HolomorphicFamily O (r + r)
        (fun z => (ℱ 0 z).prod (ℱ 1 z)) ∧
      (∀ z, z ∈ O →
        PositivePeriod (r + r)
          (fun u v => ψ 0 u.1 v.1 + ψ 1 u.2 v.2)
          (fun u => (realConj u.1, realConj u.2))
          ((ℱ 0 z).prod (ℱ 1 z))) ∧
      -- Compatibility with the rational trace form.
      (∀ (i : Fin 2) (x y : Fin 3 → E),
        ψ i (embeddingCoordinates σ x)
          (embeddingCoordinates σ y) =
        ((Algebra.trace ℚ E
          (δ * a i *
            (∑ j, ∑ k,
              x j * H j k *
                NumberField.IsCMField.complexConj E (y k)))) : ℂ)) := by
  let B := matrixB σ H
  have hBL : (fun τ x y => B τ x y) = localB σ H := by
    funext τ x y
    exact matrixB_apply σ H τ x y
  dsimp only
  rw [← hBL] at hμpos hμneg hcompact ⊢
  let O : Set BallChart :=
    {z | (B μ (lineVector z) (star (lineVector z))).re < 0}
  let r := 3 * Fintype.card Place
  let f (i : Fin 2) (z : BallChart) := globalFrame B μ (d i) z
  have hB (τ : Place) : HermitianB (B τ) := matrixB_hermitian σ H hHermitian τ
  have hn : (B μ (axis 2) (axis 2)).re < 0 := by
    have he : axis 2 = ![0, 0, 1] := by
      ext j
      fin_cases j <;> simp [axis]
    rw [he]
    exact hμneg
  have hq (z : BallChart) (hz : z ∈ O) : B μ (lineVector z) (axis 2) ≠ 0 :=
    localFrame_denominator_ne_zero (B μ) (hB μ) hμpos hn z hz
  have hO : IsOpen O := negative_domain_isOpen (B μ)
  have hXdim : Module.finrank ℂ (Place → Vec) = r := by
    simp [r, Vec, Module.finrank_pi_fintype, Nat.mul_comm]
  have hYdim : Module.finrank ℂ (Ambient Place) = r + r := by
    simp [r, Ambient, Vec, Module.finrank_pi_fintype, Module.finrank_prod]
    omega
  choose a ha0 hac has using (fun i : Fin 2 =>
    scalar_with_prescribed_signs hWeakApproximation σ hσ μ δ hδ hδc (wantedSign B μ (d i)))
  have ht (i : Fin 2) (τ : Place) : (σ τ (δ * a i)).re = 0 :=
    coefficient_real_zero (σ τ) δ (a i) hδc (hac i)
  have hperiod (i : Fin 2) (z : BallChart) (hz : z ∈ O) :
      PositivePeriod r (tracePairing (fun τ x y => B τ x y) (fun τ => σ τ (δ * a i)))
        realConj (LinearMap.range (f i z)) := by
    apply globalFrame_positivePeriod B hB μ (d i) z (hq z hz) _ (ht i)
    intro τ u hu hne
    exact wantedSign_positive B hB μ hμpos hcompact (d i) z hz (hq z hz)
      τ (σ τ (δ * a i)) (ht i τ) (has i τ) u hu hne
  refine ⟨a, (fun i z => LinearMap.range (f i z)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨ha0 i, hac i, ?_⟩
    simpa [wantedSign] using has i μ
  · intro i
    have hh := holomorphicFamily_range O hO (f i)
      (fun z _ => globalFrame_injective B μ (d i) z)
      (globalFrame_differentiable B μ (d i) O hq)
    rwa [hXdim] at hh
  · intro i z hz
    exact ⟨globalFrame_range B μ (d i) z (hq z hz), hperiod i z hz⟩
  · have hh := holomorphicFamily_range O hO
      (fun z => (f 0 z).prodMap (f 1 z))
      (fun z _ => by
        intro u v he
        exact Prod.ext
          (globalFrame_injective B μ (d 0) z (congrArg Prod.fst he))
          (globalFrame_injective B μ (d 1) z (congrArg Prod.snd he)))
      (fun v =>
        (globalFrame_differentiable B μ (d 0) O hq v.1).prodMk
          (globalFrame_differentiable B μ (d 1) O hq v.2))
    simpa only [LinearMap.range_prodMap, Module.finrank_prod, hXdim] using hh
  · intro z hz
    exact positivePeriod_prod r _ _ (realConjLinearMap Place) (realConjLinearMap Place)
      _ _ hYdim (hperiod 0 z hz) (hperiod 1 z hz)
  · intro i x y
    rw [hBL]
    exact tracePairing_rational σ hσ δ (a i) hδc (hac i) H hHermitian x y

end

end OAI.Geometry.ComplexBall.PrescribedSignsB
