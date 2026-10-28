import Mathlib

/-! # Functions Metaplectic -/

namespace OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction

noncomputable section

section

/-!
Concrete function spaces, Haar normalization, oscillatory Gaussian integrals,
and generator operators for LocalWeil. No metaplectic transformation identity is
assumed in these definitions. Archimedean Schwartz functions are transported
through continuous additive coordinates; nonarchimedean test functions are
locally constant functions with compact support.
-/

open _root_.MeasureTheory Filter
open scoped BigOperators _root_.Topology SchwartzMap

abbrev Position (k : Type) (n : ℕ) := Fin n → k
abbrev GeneralLinear (k : Type) [Field k] (n : ℕ) :=
  (Matrix (Fin n) (Fin n) k)ˣ
abbrev SymmetricMatrix (k : Type) [Field k] (n : ℕ) :=
  { B : Matrix (Fin n) (Fin n) k // B.IsSymm }

/-- The usual Bruhat space, using additive real coordinates in the
archimedean case and compact locally constant functions in the finite case. -/
def schwartzBruhat (k : Type) [NormedField k] (n : ℕ) :
    Submodule ℂ (Position k n → ℂ) :=
  Submodule.span ℂ {f |
    (IsLocallyConstant f ∧ HasCompactSupport f) ∨
    ∃ (d : ℕ) (e : (Fin d → ℝ) ≃ₜ+ Position k n)
      (φ : SchwartzMap (Fin d → ℝ) ℂ), f = fun x => φ (e.symm x)}

theorem compact_locallyConstant_mem
    {k : Type} [NormedField k] {n : ℕ} {f : Position k n → ℂ}
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    f ∈ schwartzBruhat k n :=
  Submodule.subset_span (Or.inl ⟨hf, hc⟩)

theorem schwartz_coordinate_mem
    {k : Type} [NormedField k] {n d : ℕ}
    (e : (Fin d → ℝ) ≃ₜ+ Position k n)
    (φ : SchwartzMap (Fin d → ℝ) ℂ) :
    (fun x => φ (e.symm x)) ∈ schwartzBruhat k n :=
  Submodule.subset_span (Or.inr ⟨d, e, φ, rfl⟩)

def dot {k : Type} [CommSemiring k] {n : ℕ}
    (x y : Position k n) : k := ∑ i, x i * y i

def quadratic {k : Type} [Field k] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) k) (x : Position k n) : k :=
  (∑ i, ∑ j, x i * B i j * x j) / 2

theorem quadratic_neg {k : Type} [Field k] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) k) (x : Position k n) :
    quadratic (-B) x = -quadratic B x := by
  simp [quadratic, Finset.sum_neg_distrib, neg_div]

/-- Multiplication by a quadratic character, on actual functions. -/
def quadraticOperator {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (B : Matrix (Fin n) (Fin n) k) :
    (Position k n → ℂ) ≃ₗ[ℂ] (Position k n → ℂ) where
  toFun f x := ψ (quadratic B x) * f x
  invFun f x := ψ (-quadratic B x) * f x
  left_inv f := by
    funext x
    change ψ (-quadratic B x) * (ψ (quadratic B x) * f x) = f x
    rw [← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  right_inv f := by
    funext x
    change ψ (quadratic B x) * (ψ (-quadratic B x) * f x) = f x
    rw [← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  map_add' f g := by funext x; exact mul_add _ _ _
  map_smul' c f := by funext x; exact mul_left_comm _ _ _

theorem quadraticOperator_apply {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (B : Matrix (Fin n) (Fin n) k)
    (f : Position k n → ℂ) (x : Position k n) :
    quadraticOperator ψ B f x = ψ (quadratic B x) * f x := rfl

/-- Inverse linear substitution. The determinant factor is separate. -/
def substitutionOperator {k : Type} [Field k] {n : ℕ}
    (A : GeneralLinear k n) :
    (Position k n → ℂ) ≃ₗ[ℂ] (Position k n → ℂ) where
  toFun f x := f (Matrix.mulVec (↑(A⁻¹)) x)
  invFun f x := f (Matrix.mulVec (↑A) x)
  left_inv f := by
    funext x
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec]
  right_inv f := by
    funext x
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem substitutionOperator_apply {k : Type} [Field k] {n : ℕ}
    (A : GeneralLinear k n) (f : Position k n → ℂ) (x : Position k n) :
    substitutionOperator A f x = f (Matrix.mulVec (↑(A⁻¹)) x) := rfl

/-- Fourier integral with the negative-sign convention. -/
def fourierIntegral {k : Type} [Field k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Position k n))
    (f : Position k n → ℂ) (x : Position k n) : ℂ :=
  ∫ y, f y * ψ (-dot x y) ∂μ

theorem fourierIntegral_zero
    {k : Type} [Field k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Position k n)) :
    fourierIntegral ψ μ 0 = 0 := by
  funext x
  simp [fourierIntegral]

theorem fourierIntegral_smul
    {k : Type} [Field k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Position k n))
    (c : ℂ) (f : Position k n → ℂ) :
    fourierIntegral ψ μ (c • f) = c • fourierIntegral ψ μ f := by
  funext x
  simp only [fourierIntegral, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem fourierIntegral_add
    {k : Type} [Field k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Position k n))
    (f g : Position k n → ℂ) (x : Position k n)
    (hf : Integrable (fun y => f y * ψ (-dot x y)) μ)
    (hg : Integrable (fun y => g y * ψ (-dot x y)) μ) :
    fourierIntegral ψ μ (f + g) x =
      fourierIntegral ψ μ f x + fourierIntegral ψ μ g x := by
  simp only [fourierIntegral, Pi.add_apply, add_mul]
  exact integral_add hf hg

/-- Extract the phase of a complex scalar. Nonvanishing of the local
oscillatory Gaussian is a mathematical conclusion, not a data field. -/
def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem phase_norm {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp [phase, Complex.norm_real,
    norm_ne_zero_iff.mpr hz]

theorem phase_ne_zero {z : ℂ} (hz : z ≠ 0) : phase z ≠ 0 := by
  intro h
  have := phase_norm hz
  simp [h] at this

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

/-- A positive compact set fixes a reference test function for Plancherel
normalization. The resulting self-dual measure is independent of this choice. -/
def referenceCompact : TopologicalSpace.PositiveCompacts k :=
  Classical.choice inferInstance

def referenceFourier (ψ : AddChar k ℂ) (ξ : k) : ℂ :=
  ∫ x in (referenceCompact k : Set k), ψ (-(ξ * x))
    ∂(Measure.addHaar : Measure k)

/-- The square of the scale relating reference Haar measure to self-dual
Haar measure, computed from the Fourier L² norm of a compact indicator. -/
def fourierHaarScaleSquared (ψ : AddChar k ℂ) : ℝ :=
  (∫ ξ, ‖referenceFourier k ψ ξ‖ ^ 2 ∂(Measure.addHaar : Measure k)) /
    (Measure.addHaar : Measure k).real (referenceCompact k : Set k)

def selfDualMeasure (ψ : AddChar k ℂ) : Measure k :=
  ENNReal.ofReal ((Real.sqrt (fourierHaarScaleSquared k ψ))⁻¹) • Measure.addHaar

def positionMeasure (n : ℕ) (ψ : AddChar k ℂ) : Measure (Position k n) :=
  Measure.pi (fun _ : Fin n => selfDualMeasure k ψ)

/-- The local absolute value is the Haar modulus, including the squared
complex absolute value at a complex place. -/
def localModulus (a : kˣ) : ℝ :=
  MeasureTheory.distribHaarChar k a

omit [MeasurableSpace k] [BorelSpace k] in
theorem localModulus_pos (a : kˣ) : 0 < localModulus k a :=
  MeasureTheory.distribHaarChar_pos

omit [MeasurableSpace k] [BorelSpace k] in
theorem localModulus_mul (a b : kˣ) :
    localModulus k (a * b) = localModulus k a * localModulus k b := by
  simp [localModulus, map_mul]

omit [MeasurableSpace k] [BorelSpace k] in
theorem localModulus_one : localModulus k 1 = 1 := by
  simp [localModulus]

omit [MeasurableSpace k] [BorelSpace k] in
theorem localModulus_inv (a : kˣ) : localModulus k a⁻¹ = (localModulus k a)⁻¹ := by
  simp [localModulus, map_inv]

/-- Abel regularization of the one-dimensional oscillatory Gaussian. -/
def regularizedGaussian (ψ : AddChar k ℂ) (a : k) (ε : ℝ) : ℂ :=
  ∫ x : k, (Real.exp (-ε * ‖x‖ ^ 2) : ℂ) * ψ (a * x ^ 2 / 2)
    ∂(Measure.addHaar : Measure k)

def gaussianIntegral (ψ : AddChar k ℂ) (a : k) : ℂ :=
  Filter.limUnder (𝓝[>] (0 : ℝ)) (regularizedGaussian k ψ a)

/-- The unnormalized Weil index of the quadratic form a x²/2. -/
def gaussianIndex (ψ : AddChar k ℂ) (a : k) : ℂ :=
  phase (gaussianIntegral k ψ a)

theorem gaussianIndex_norm (ψ : AddChar k ℂ) (a : k)
    (ha : gaussianIntegral k ψ a ≠ 0) :
    ‖gaussianIndex k ψ a‖ = 1 := phase_norm ha

def determinantUnit {n : ℕ} (A : GeneralLinear k n) : kˣ :=
  Units.map (Matrix.detMonoidHom : Matrix (Fin n) (Fin n) k →* k) A

def leviFactor {n : ℕ} (ψ : AddChar k ℂ) (A : GeneralLinear k n) : ℂ :=
  (gaussianIndex k ψ (determinantUnit k A) / gaussianIndex k ψ 1) *
    ((Real.sqrt (localModulus k (determinantUnit k A)))⁻¹ : ℂ)

def leviOperator {n : ℕ} (ψ : AddChar k ℂ) (A : GeneralLinear k n) :
    (Position k n → ℂ) →ₗ[ℂ] (Position k n → ℂ) :=
  leviFactor k ψ A • (substitutionOperator A).toLinearMap

def weylOperator (n : ℕ) (ψ : AddChar k ℂ) (f : Position k n → ℂ) :
    Position k n → ℂ :=
  (gaussianIndex k ψ 1 ^ n)⁻¹ • fourierIntegral ψ (positionMeasure k n ψ) f

end

section

/-!
The oscillator extension is constructed independently of its generator
formulas: its elements are symplectic transformations and L²-isometric
linear automorphisms of the Bruhat space intertwining the Heisenberg action.
The bare metaplectic subgroup is generated by commutators and the central
operator -1. Including -1 also retains the split double cover at complex
places. Proving that its projection is a double cover, and identifying the
explicit generators in it, are conclusions of LocalWeil rather than input fields.
-/

open _root_.MeasureTheory
open scoped BigOperators

abbrev PhaseSpace (k : Type) (n : ℕ) := (Fin n ⊕ Fin n) → k
abbrev Symplectic (k : Type) [Field k] (n : ℕ) := Matrix.symplecticGroup (Fin n) k

def symplecticAction {k : Type} [Field k] {n : ℕ}
    (g : Symplectic k n) (v : PhaseSpace k n) : PhaseSpace k n :=
  Matrix.mulVec (g : Matrix _ _ k) v

@[simp] theorem symplecticAction_one {k : Type} [Field k] {n : ℕ}
    (v : PhaseSpace k n) : symplecticAction (1 : Symplectic k n) v = v :=
  Matrix.one_mulVec v

theorem symplecticAction_mul {k : Type} [Field k] {n : ℕ}
    (g h : Symplectic k n) (v : PhaseSpace k n) :
    symplecticAction (g * h) v = symplecticAction g (symplecticAction h v) := by
  exact (Matrix.mulVec_mulVec v
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)).symm

@[simp] theorem symplecticAction_inv_cancel {k : Type} [Field k] {n : ℕ}
    (g : Symplectic k n) (v : PhaseSpace k n) :
    symplecticAction g (symplecticAction g⁻¹ v) = v := by
  rw [← symplecticAction_mul, mul_inv_cancel, symplecticAction_one]

@[simp] theorem symplecticAction_cancel_inv {k : Type} [Field k] {n : ℕ}
    (g : Symplectic k n) (v : PhaseSpace k n) :
    symplecticAction g⁻¹ (symplecticAction g v) = v := by
  rw [← symplecticAction_mul, inv_mul_cancel, symplecticAction_one]

/-- The Weyl form of the Schrödinger Heisenberg operator:
ψ(p·(x-q/2)) f(x-q). Complex linearity accounts for the central coordinate. -/
def heisenbergFunction {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (v : PhaseSpace k n) (f : Position k n → ℂ) :
    Position k n → ℂ := fun x =>
  ψ (∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2)) *
    f (fun i => x i - v (Sum.inl i))

theorem heisenbergFunction_neg {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (v : PhaseSpace k n) (f : Position k n → ℂ) :
    heisenbergFunction ψ v (-f) = -heisenbergFunction ψ v f := by
  funext x
  simp [heisenbergFunction]

def heisenbergGraph {k : Type} [NormedField k] {n : ℕ}
    (ψ : AddChar k ℂ) (v : PhaseSpace k n) (f h : schwartzBruhat k n) : Prop :=
  h.val = heisenbergFunction ψ v f.val

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] (n : ℕ)

/-- Reference L² energy. Rescaling Haar measure does not change which
linear automorphisms are unitary. -/
def l2Energy (f : schwartzBruhat k n) : ℝ :=
  ∫ x, ‖f.val x‖ ^ 2 ∂(Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k)))

theorem l2Energy_neg (f : schwartzBruhat k n) :
    l2Energy k n (-f) = l2Energy k n f := by
  simp [l2Energy]

/-- The independently defined Heisenberg intertwiner extension. The
graph formulation avoids presupposing stability lemmas for test functions. -/
def oscillatorSubgroup (ψ : AddChar k ℂ) :
    Subgroup (Symplectic k n × (schwartzBruhat k n ≃ₗ[ℂ] schwartzBruhat k n)) where
  carrier := {a |
    (∀ f, l2Energy k n (a.2 f) = l2Energy k n f) ∧
    ∀ v f h, heisenbergGraph ψ v f h ↔
      heisenbergGraph ψ (symplecticAction a.1 v) (a.2 f) (a.2 h)}
  one_mem' := by
    constructor
    · intro f; rfl
    · intro v f h
      change heisenbergGraph ψ v f h ↔ heisenbergGraph ψ (symplecticAction 1 v) f h
      rw [symplecticAction_one]
  mul_mem' := by
    intro a b ha hb
    constructor
    · intro f
      change l2Energy k n (a.2 (b.2 f)) = l2Energy k n f
      rw [ha.1, hb.1]
    · intro v f h
      change heisenbergGraph ψ v f h ↔
        heisenbergGraph ψ (symplecticAction (a.1 * b.1) v)
          (a.2 (b.2 f)) (a.2 (b.2 h))
      rw [symplecticAction_mul]
      exact (hb.2 v f h).trans (ha.2 _ _ _)
  inv_mem' := by
    intro a ha
    constructor
    · intro f
      have h := ha.1 (a.2.symm f)
      simpa using h.symm
    · intro v f h
      have hh := ha.2 (symplecticAction a.1⁻¹ v) (a.2.symm f) (a.2.symm h)
      simpa using hh.symm

abbrev Oscillator (ψ : AddChar k ℂ) := oscillatorSubgroup k n ψ

/-- The actual negative identity operator, not a formal sign symbol. -/
def oscillatorMinus (ψ : AddChar k ℂ) : Construction.Oscillator k n ψ := by
  refine ⟨(1, LinearEquiv.neg ℂ), ?_⟩
  constructor
  · exact l2Energy_neg k n
  · intro v f h
    change (h.val = heisenbergFunction ψ v f.val) ↔
      -h.val = heisenbergFunction ψ (symplecticAction 1 v) (-f.val)
    rw [symplecticAction_one, heisenbergFunction_neg, neg_inj]

/-- Intrinsic bare subgroup of the oscillator extension. This definition
does not mention linear substitution, quadratic, or Fourier generators. -/
def metaplecticSubgroup (ψ : AddChar k ℂ) : Subgroup (Construction.Oscillator k n ψ) :=
  Subgroup.closure (commutatorSet (Construction.Oscillator k n ψ) ∪ {oscillatorMinus k n ψ})

abbrev Metaplectic (ψ : AddChar k ℂ) := metaplecticSubgroup k n ψ

def metaplecticProjection (ψ : AddChar k ℂ) : Metaplectic k n ψ →* Symplectic k n :=
  (MonoidHom.fst _ _).comp
    ((oscillatorSubgroup k n ψ).subtype.comp (metaplecticSubgroup k n ψ).subtype)

/-- The genuine linear action is the operator component of the constructed group. -/
def weilRepresentation (ψ : AddChar k ℂ) :
    Metaplectic k n ψ →* (schwartzBruhat k n ≃ₗ[ℂ] schwartzBruhat k n) :=
  (MonoidHom.snd _ _).comp
    ((oscillatorSubgroup k n ψ).subtype.comp (metaplecticSubgroup k n ψ).subtype)

theorem weilRepresentation_unitary (ψ : AddChar k ℂ)
    (g : Metaplectic k n ψ) (f : schwartzBruhat k n) :
    l2Energy k n (weilRepresentation k n ψ g f) = l2Energy k n f :=
  g.val.property.1 f

theorem weilRepresentation_intertwines (ψ : AddChar k ℂ)
    (g : Metaplectic k n ψ) (v : PhaseSpace k n) (f h : schwartzBruhat k n) :
    heisenbergGraph ψ v f h ↔
      heisenbergGraph ψ (symplecticAction (metaplecticProjection k n ψ g) v)
        (weilRepresentation k n ψ g f) (weilRepresentation k n ψ g h) :=
  g.val.property.2 v f h

def metaplecticMinus (ψ : AddChar k ℂ) : Metaplectic k n ψ :=
  ⟨oscillatorMinus k n ψ, Subgroup.subset_closure (Or.inr rfl)⟩

theorem metaplecticMinus_projection (ψ : AddChar k ℂ) :
    metaplecticProjection k n ψ (metaplecticMinus k n ψ) = 1 := rfl

theorem metaplecticMinus_action (ψ : AddChar k ℂ) (f : schwartzBruhat k n) :
    weilRepresentation k n ψ (metaplecticMinus k n ψ) f = -f := rfl

end

/-! Analytic properties of the concrete Bruhat space used by LocalWeil. -/

open _root_.MeasureTheory
open scoped ENNReal SchwartzMap

theorem localField_proper
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    (h : ¬ DiscreteTopology k) : ProperSpace k := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (h hd).elim
  · exact ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k

theorem localField_secondCountable
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    (h : ¬ DiscreteTopology k) : SecondCountableTopology k := by
  let : ProperSpace k := localField_proper k h
  infer_instance

theorem schwartzBruhat_continuous
    {k : Type} [NormedField k] {n : ℕ}
    {f : Position k n → ℂ} (hf : f ∈ schwartzBruhat k n) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, e, φ, rfl⟩
      · exact hf.1.continuous
      · exact φ.continuous.comp e.symm.continuous
  | zero => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact continuous_const.smul hf

theorem schwartzBruhat_memLp
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    [SecondCountableTopology k]
    (μ : Measure (Position k n)) [μ.IsAddHaarMeasure] (p : ℝ≥0∞)
    {f : Position k n → ℂ} (hf : f ∈ schwartzBruhat k n) : MemLp f p μ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, e, φ, rfl⟩
      · exact hf.1.continuous.memLp_of_hasCompactSupport hf.2
      · let : (μ.map e.symm).IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
        exact (φ.memLp p (μ.map e.symm)).comp_of_map
          e.symm.continuous.measurable.aemeasurable
  | zero => exact MemLp.zero
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

theorem schwartzBruhat_integrable
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    [SecondCountableTopology k]
    (μ : Measure (Position k n)) [μ.IsAddHaarMeasure]
    (f : schwartzBruhat k n) : Integrable f.val μ :=
  memLp_one_iff_integrable.mp (schwartzBruhat_memLp μ 1 f.property)

theorem schwartzBruhat_norm_sq_integrable
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    [SecondCountableTopology k]
    (μ : Measure (Position k n)) [μ.IsAddHaarMeasure]
    (f : schwartzBruhat k n) : Integrable (fun x => ‖f.val x‖ ^ 2) μ :=
  (schwartzBruhat_memLp μ 2 f.property).integrable_norm_pow (by decide)

theorem schwartzBruhat_integral_norm_sq_eq_zero_iff
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (μ : Measure (Position k n)) [μ.IsAddHaarMeasure]
    (f : schwartzBruhat k n) :
    (∫ x, ‖f.val x‖ ^ 2 ∂μ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun x => sq_nonneg ‖f.val x‖) (schwartzBruhat_norm_sq_integrable μ f)).mp h
    have hf : f.val =ᵐ[μ] 0 := by
      filter_upwards [hae] with x hx
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
    apply Subtype.ext
    exact Measure.eq_of_ae_eq hf (schwartzBruhat_continuous f.property) continuous_const
  · rintro rfl
    simp

theorem l2Energy_eq_zero_iff
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (h : ¬ DiscreteTopology k) (n : ℕ) (f : schwartzBruhat k n) :
    l2Energy k n f = 0 ↔ f = 0 := by
  let : SecondCountableTopology k := localField_secondCountable k h
  exact schwartzBruhat_integral_norm_sq_eq_zero_iff
    (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))) f

/-- Additive coordinate changes preserve the actual test space. -/
theorem schwartzBruhat_comp_addEquiv
    {k : Type} [NormedField k] {m n : ℕ}
    (e : Position k m ≃ₜ+ Position k n)
    {f : Position k n → ℂ} (hf : f ∈ schwartzBruhat k n) :
    f ∘ e ∈ schwartzBruhat k m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, a, φ, rfl⟩
      · exact compact_locallyConstant_mem
          (hf.1.comp_continuous e.continuous) (hf.2.comp_homeomorph e.toHomeomorph)
      · exact schwartz_coordinate_mem (a.trans e.symm) φ
  | zero => exact (schwartzBruhat k m).zero_mem
  | add f g _ _ hf hg => exact (schwartzBruhat k m).add_mem hf hg
  | smul c f _ hf => exact (schwartzBruhat k m).smul_mem c hf

def schwartzBruhat_coordinateEquiv
    {k : Type} [NormedField k] {m n : ℕ}
    (e : Position k m ≃ₜ+ Position k n) :
    schwartzBruhat k n ≃ₗ[ℂ] schwartzBruhat k m where
  toFun f := ⟨f.val ∘ e, schwartzBruhat_comp_addEquiv e f.property⟩
  invFun f := ⟨f.val ∘ e.symm, schwartzBruhat_comp_addEquiv e.symm f.property⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction
