import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion
import Lean.Util.CollectAxioms

/-! # Poisson Automorphy Normalization Data -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
section

/-! Continuous determinant square roots on the full Siegel domain.
The branch is fixed by the principal logarithm at `i I`, then continued
over the convex domain. No theta identity is used in this construction. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def siegelSet (ι : Type*) [Fintype ι] : Set (Matrix ι ι ℂ) :=
  {Z | Z.IsSymm ∧ Matrix.PosDef (fun i j => (Z i j).im)}

abbrev Domain (ι : Type*) [Fintype ι] := ↥(siegelSet ι)

def toSiegel (Z : Domain ι) : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι :=
  ⟨Z.val, Z.property.1, Z.property.2⟩

def ofSiegel (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) : Domain ι :=
  ⟨Z.matrix, Z.symmetric, Z.imaginary_posDef⟩

def basePeriod (ι : Type*) [Fintype ι] [DecidableEq ι] : Domain ι :=
  ⟨Matrix.diagonal (fun _ => Complex.I), Matrix.isSymm_diagonal _, by
    have him : (fun i j : ι =>
        (Matrix.diagonal (fun _ : ι => Complex.I) i j).im) =
        (1 : Matrix ι ι ℝ) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [him]
    exact Matrix.PosDef.one⟩

omit [DecidableEq ι] in
theorem siegelSet_convex : Convex ℝ (siegelSet ι) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨(hX.1.smul a).add (hY.1.smul b), ?_⟩
  have him :
      (fun i j => ((a • X + b • Y) i j).im) =
        a • (fun i j => (X i j).im) + b • (fun i j => (Y i j).im) := by
    ext i j
    simp [Complex.real_smul]
  rw [him]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb' : b = 1 := by linarith
    simpa [hb'] using hY.2
  · exact (hX.2.smul ha').add_posSemidef (hY.2.posSemidef.smul hb)

instance domainContractible : ContractibleSpace (Domain ι) :=
  siegelSet_convex.contractibleSpace ⟨(basePeriod ι).val, (basePeriod ι).property⟩

instance domainLocallyPathConnected : LocallyPathConnectedSpace (Domain ι) := by
  let : LocallyConvexSpace ℝ (Matrix ι ι ℂ) :=
    NormedSpace.toLocallyConvexSpace
  exact siegelSet_convex.locallyPathConnectedSpace

def denominatorDet (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : Domain ι) : ℂ :=
  (g.complexify.denominator Z.val).det

theorem denominatorDet_ne_zero (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : Domain ι) :
    denominatorDet g Z ≠ 0 :=
  (g.denominator_det_isUnit (toSiegel Z)).ne_zero

theorem denominatorDet_continuous (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) :
    Continuous (denominatorDet g) := by
  unfold denominatorDet AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator
  fun_prop

/-- The logarithm lift is uniquely fixed at the base period. -/
theorem existsUnique_normalizedLog (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) :
    ∃! L : C(Domain ι, ℂ),
      L (basePeriod ι) = Complex.log (denominatorDet g (basePeriod ι)) ∧
      ∀ Z, Complex.exp (L Z) = denominatorDet g Z := by
  obtain ⟨L, ⟨hbase, hL⟩, huniq⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
      ⟨denominatorDet g, denominatorDet_continuous g⟩
      (Complex.exp_log (denominatorDet_ne_zero g (basePeriod ι)))
      (fun Z => by simpa using denominatorDet_ne_zero g Z)
  refine ⟨L, ⟨hbase, fun Z => congrFun hL Z⟩, ?_⟩
  intro M hM
  exact huniq M ⟨hM.1, funext hM.2⟩

def normalizedLog (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) : C(Domain ι, ℂ) :=
  (existsUnique_normalizedLog g).exists.choose

theorem normalizedLog_base (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) :
    normalizedLog g (basePeriod ι) =
      Complex.log (denominatorDet g (basePeriod ι)) :=
  (existsUnique_normalizedLog g).exists.choose_spec.1

theorem exp_normalizedLog (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : Domain ι) :
    Complex.exp (normalizedLog g Z) = denominatorDet g Z :=
  (existsUnique_normalizedLog g).exists.choose_spec.2 Z

def halfDetDomain (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : Domain ι) : ℂ :=
  Complex.exp (normalizedLog g Z / 2)

def halfDet (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) : ℂ :=
  halfDetDomain g (ofSiegel Z)

theorem halfDetDomain_sq (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : Domain ι) :
    halfDetDomain g Z ^ 2 = denominatorDet g Z := by
  rw [halfDetDomain, ← Complex.exp_nat_mul]
  convert exp_normalizedLog g Z using 1
  congr 1
  ring

theorem halfDet_sq (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    halfDet g Z ^ 2 = (g.complexify.denominator Z.matrix).det :=
  halfDetDomain_sq g (ofSiegel Z)

theorem halfDet_ne_zero (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    halfDet g Z ≠ 0 := Complex.exp_ne_zero _

theorem halfDetDomain_continuous (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) :
    Continuous (halfDetDomain g) := by
  unfold halfDetDomain
  fun_prop

theorem halfDet_base (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) :
    halfDet g (toSiegel (basePeriod ι)) =
      Complex.exp (Complex.log (denominatorDet g (basePeriod ι)) / 2) := by
  change Complex.exp (normalizedLog g (basePeriod ι) / 2) = _
  rw [normalizedLog_base]

theorem halfDet_norm (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    ‖halfDet g Z‖ = Real.sqrt ‖(g.complexify.denominator Z.matrix).det‖ := by
  have h : ‖halfDet g Z‖ ^ 2 = ‖(g.complexify.denominator Z.matrix).det‖ := by
    rw [← norm_pow, halfDet_sq]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem halfDetDomain_unique (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (f : C(Domain ι, ℂ))
    (hsq : ∀ Z, f Z ^ 2 = denominatorDet g Z)
    (hbase : f (basePeriod ι) = halfDetDomain g (basePeriod ι)) :
    ∀ Z, f Z = halfDetDomain g Z := by
  obtain ⟨_, _, huniq⟩ :=
    (isCoveringMapOn_npow (𝕜 := ℂ) 2 (by norm_num)).existsUnique_continuousMap_lifts
      ⟨denominatorDet g, denominatorDet_continuous g⟩
      (halfDetDomain_sq g (basePeriod ι))
      (fun Z => by simpa using denominatorDet_ne_zero g Z)
  have h₁ := huniq f ⟨hbase, funext hsq⟩
  have h₂ := huniq ⟨halfDetDomain g, halfDetDomain_continuous g⟩
    ⟨rfl, funext (halfDetDomain_sq g)⟩
  intro Z
  exact congrArg (fun F : C(Domain ι, ℂ) => F Z) (h₁.trans h₂.symm)

/-- A total extension used only to express differentiability within the
Siegel domain in the ambient complex matrix space. -/
def halfDetExtension (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (M : Matrix ι ι ℂ) : ℂ :=
  if h : M ∈ siegelSet ι then halfDetDomain g ⟨M, h⟩ else 0

theorem halfDetExtension_continuousOn (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) :
    ContinuousOn (halfDetExtension g) (siegelSet ι) := by
  rw [continuousOn_iff_continuous_domRestrict]
  simpa [halfDetExtension, Set.domRestrict_def] using halfDetDomain_continuous g

theorem halfDetExtension_sq (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ)
    {M : Matrix ι ι ℂ} (hM : M ∈ siegelSet ι) :
    halfDetExtension g M ^ 2 = (g.complexify.denominator M).det := by
  simpa [halfDetExtension, hM, denominatorDet] using halfDetDomain_sq g ⟨M, hM⟩

/-- Holomorphy follows from the analytic local inverse of squaring at a
nonzero square root. This does not assume a Gaussian integral formula. -/
theorem halfDetExtension_differentiableOn (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) :
    DifferentiableOn ℂ (halfDetExtension g) (siegelSet ι) := by
  intro M hM
  let c := halfDetExtension g M
  have hc : c ≠ 0 := by
    simp [c, halfDetExtension, hM, halfDetDomain]
  have hder : HasStrictDerivAt (fun z : ℂ => z ^ 2) (2 * c) c := by
    simpa using hasStrictDerivAt_pow 2 c
  have hder0 : 2 * c ≠ 0 := mul_ne_zero (by norm_num) hc
  let inv := hder.localInverse _ _ _ hder0
  have hinv : DifferentiableAt ℂ inv (c ^ 2) :=
    (hder.to_localInverse hder0).hasDerivAt.differentiableAt
  have hdet : Differentiable ℂ (fun N : Matrix ι ι ℂ =>
      (g.complexify.denominator N).det) := by
    simp only [Matrix.det_apply', AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator,
      Matrix.add_apply, Matrix.mul_apply]
    fun_prop
  have hs := halfDetExtension_sq g hM
  have hcomp : DifferentiableWithinAt ℂ
      (fun N => inv ((g.complexify.denominator N).det)) (siegelSet ι) M := by
    have hinv' : DifferentiableAt ℂ inv (g.complexify.denominator M).det := by
      simpa only [← hs] using hinv
    exact hinv'.comp_differentiableWithinAt M (hdet M).differentiableWithinAt
  have heq : (fun N => inv ((g.complexify.denominator N).det)) =ᶠ[
      nhdsWithin M (siegelSet ι)] halfDetExtension g := by
    have hcont := halfDetExtension_continuousOn g M hM
    have hlocal := hder.eventually_left_inverse hder0
    filter_upwards [hcont hlocal, self_mem_nhdsWithin] with N hN hNs
    rw [← halfDetExtension_sq g hNs]
    exact hN
  exact hcomp.congr_of_eventuallyEq_of_mem heq.symm hM

/-- The unit phase at the base period; the positive modulus is separate. -/
def basePhase (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) : ℂ :=
  halfDet g (toSiegel (basePeriod ι)) /
    (‖halfDet g (toSiegel (basePeriod ι))‖ : ℂ)

theorem basePhase_norm (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) : ‖basePhase g‖ = 1 := by
  rw [basePhase, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (halfDet_ne_zero g _))

def quadraticFactor (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : ℂ :=
  Complex.exp (g.thetaCorrectionForm Z z z)

theorem quadraticFactor_zero (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    quadraticFactor g Z 0 = 1 := by simp [quadraticFactor]

theorem quadraticFactor_ne_zero (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : quadraticFactor g Z z ≠ 0 :=
  Complex.exp_ne_zero _

theorem quadraticFactor_formula (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    quadraticFactor g Z z = Complex.exp
      ((Real.pi : ℂ) * Complex.I *
        (z ⬝ᵥ (((g.complexify.denominator Z.matrix)⁻¹ * g.complexify.C) *ᵥ z))) := by
  rw [quadraticFactor, g.thetaCorrectionForm_apply]

end

/-!
# PoissonAutomorphy's explicit Schrödinger data

For ℚ we use the concrete adelic coordinates ℝ × 𝔸_f. Test functions are
finite sums of tensors of actual real Schwartz functions and locally constant
compactly supported finite functions. All operators act on these spaces.

The hypotheses specify genuine two-fold operator covers, Heisenberg
intertwining, self-dual measure, a rational splitting with its three
Schrödinger generator formulas, and tensor factorization. None mention a
theta functional or a sum over rational points.

The real cover's scalar normalization is specified by its matrix coefficient
at the standard Gaussian and zero. This is the usual concrete realization of
the two real metaplectic intertwiners above a symplectic matrix. We construct
the choice of its sign from the determinant root, rather than assume a
Gaussian transformation formula. Existence of an independently supplied
Weil representation is a natural input, not an asserted canonical constant.

LocalWeil's repaired construction uses (position,momentum) coordinates. Here a symplectic matrix
acts on (momentum,position): LocalWeil's lower unipotent becomes our upper
unipotent, and its negative Fourier transform covers our matrix (0,-1;1,0).
The `coordinateSwap_conjugation` lemma below verifies this convention change.
No LocalWeil target or construction is assumed as an established canonical cover.
-/

open scoped _root_.Matrix
open _root_.Matrix _root_.MeasureTheory OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM

abbrev AQf := IsDedekindDomain.FiniteAdeleRing ℤ ℚ
abbrev AQ := ℝ × AQf

instance finiteAdeleMeasurableSpace : MeasurableSpace AQf := borel AQf
instance finiteAdeleBorelSpace : BorelSpace AQf := ⟨rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Sp (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type*) [CommRing K] := Matrix.symplecticGroup ι K

def mapSp {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) :
    Sp ι K →* Sp ι L where
  toFun g := ⟨g.val.map f, SymplecticGroup.map_mem g.property f⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul

def blocks {K : Type*} [CommRing K] (g : Sp ι K) : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι K where
  A := g.val.toBlocks₁₁
  B := g.val.toBlocks₁₂
  C := g.val.toBlocks₂₁
  D := g.val.toBlocks₂₂
  symplectic := by simpa only [Matrix.fromBlocks_toBlocks] using g.property

def realBlocks (γ : Sp ι ℚ) : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ :=
  blocks (mapSp (algebraMap ℚ ℝ) γ)

/-- Coordinate change from LocalWeil's (position,momentum) to (momentum,position).
This matrix is used for conjugation, not asserted to be symplectic itself. -/
def coordinateSwap {K : Type*} [CommRing K] : Matrix (Sum ι ι) (Sum ι ι) K :=
  Matrix.fromBlocks 0 1 1 0

theorem coordinateSwap_conjugation {K : Type*} [CommRing K]
    (A B C D : Matrix ι ι K) :
    coordinateSwap * Matrix.fromBlocks A B C D * coordinateSwap =
      Matrix.fromBlocks D C B A := by
  simp [coordinateSwap, Matrix.fromBlocks_multiply]

/-- LocalWeil's lower quadratic generator becomes the upper Siegel generator. -/
theorem e23_quadratic_coordinates {K : Type*} [CommRing K]
    (B : Matrix ι ι K) :
    coordinateSwap * Matrix.fromBlocks 1 0 B 1 * coordinateSwap =
      Matrix.fromBlocks 1 B 0 1 := coordinateSwap_conjugation 1 0 B 1

/-- Both results use a negative Fourier kernel; only the coordinate order changes. -/
theorem e23_fourier_coordinates {K : Type*} [CommRing K] :
    (coordinateSwap : Matrix (Sum ι ι) (Sum ι ι) K) *
        Matrix.fromBlocks 0 1 (-1) 0 * coordinateSwap =
      Matrix.fromBlocks 0 (-1) 1 0 := coordinateSwap_conjugation 0 1 (-1) 0

def finiteSchwartz (ι : Type*) [Fintype ι] :
    Submodule ℂ ((ι → AQf) → ℂ) :=
  Submodule.span ℂ {f | IsLocallyConstant f ∧ HasCompactSupport f}

def realSchwartz (ι : Type*) [Fintype ι] :
    Submodule ℂ ((ι → ℝ) → ℂ) :=
  Submodule.span ℂ {f | ∃ φ : SchwartzMap (ι → ℝ) ℂ, f = φ}

def pureTensor (f : realSchwartz ι) (φ : finiteSchwartz ι)
    (x : ι → AQ) : ℂ := f.val (fun i => (x i).1) * φ.val (fun i => (x i).2)

def adelicSchwartz (ι : Type*) [Fintype ι] :
    Submodule ℂ ((ι → AQ) → ℂ) :=
  Submodule.span ℂ {F | ∃ f : realSchwartz ι, ∃ φ : finiteSchwartz ι,
    F = pureTensor f φ}

def tensor (f : realSchwartz ι) (φ : finiteSchwartz ι) : adelicSchwartz ι :=
  ⟨pureTensor f φ, Submodule.subset_span ⟨f, φ, rfl⟩⟩

def standardRealCharacter : AddChar ℝ ℂ :=
  Circle.coeHom.compAddChar Real.fourierChar

theorem standardRealCharacter_apply (t : ℝ) :
    standardRealCharacter t =
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := rfl

theorem standardRealCharacter_unitary (t : ℝ) :
    ‖standardRealCharacter t‖ = 1 := Circle.norm_coe (Real.fourierChar t)

def fourier {K : Type*} [CommRing K] [MeasurableSpace K]
    (ψ : AddChar K ℂ) (μ : Measure (ι → K))
    (f : (ι → K) → ℂ) (x : ι → K) : ℂ :=
  ∫ y, f y * ψ (-(∑ i, x i * y i)) ∂μ

def heisenberg {K : Type*} [CommRing K] [Algebra ℚ K]
    (ψ : AddChar K ℂ) (p q : ι → K) (f : (ι → K) → ℂ)
    (x : ι → K) : ℂ :=
  ψ (∑ i, p i * (x i - algebraMap ℚ K (1 / 2) * q i)) *
    f (fun i => x i - q i)

/-- Covariance for actual Heisenberg translates that lie in the test space.
The condition is pointwise and contains no rational summation operation. -/
def IntertwinesHeisenberg {K : Type*} [CommRing K] [Algebra ℚ K]
    (ψ : AddChar K ℂ) (S : Submodule ℂ ((ι → K) → ℂ))
    (g : Sp ι K) (T : S ≃ₗ[ℂ] S) : Prop :=
  ∀ (p q : ι → K) (f h : S),
    (∀ x, h.val x = heisenberg ψ p q f.val x) →
    ∀ x, (T h).val x =
      heisenberg ψ
        (fun i => (g.val *ᵥ Sum.elim p q) (Sum.inl i))
        (fun i => (g.val *ᵥ Sum.elim p q) (Sum.inr i)) (T f).val x

/-- A genuine two-fold cover realized by unitary Schrödinger intertwiners. -/
structure SchrodingerCover (K : Type*) [CommRing K] [Algebra ℚ K]
    [MeasurableSpace K] (ψ : AddChar K ℂ) (μ : Measure (ι → K))
    (S : Submodule ℂ ((ι → K) → ℂ)) (Mp : Type*) [Group Mp] where
  project : Mp →* Sp ι K
  action : Mp →* (S ≃ₗ[ℂ] S)
  surjective : Function.Surjective project
  negOne : Mp
  negOne_ne_one : negOne ≠ 1
  project_negOne : project negOne = 1
  kernel : ∀ m, project m = 1 ↔ m = 1 ∨ m = negOne
  genuine : ∀ f : S, action negOne f = -f
  faithful : Function.Injective (fun m => (project m, action m))
  intertwines : ∀ m, IntertwinesHeisenberg ψ S (project m) (action m)
  unitary : ∀ (m : Mp) (f h : S),
    (∫ x, (action m f).val x * star ((action m h).val x) ∂μ) =
      ∫ x, f.val x * star (h.val x) ∂μ

def adelicMeasure (μ : Measure (ι → AQf)) : Measure (ι → AQ) :=
  Measure.map (fun x : (ι → ℝ) × (ι → AQf) => fun i => (x.1 i, x.2 i))
    (volume.prod μ)

structure WeilData (ι : Type*) [Fintype ι] [DecidableEq ι]
    (MpR MpF MpA : Type*) [Group MpR] [Group MpF] [Group MpA] where
  character : AddChar AQ ℂ
  character_continuous : Continuous character
  character_unitary : ∀ x, ‖character x‖ = 1
  character_rational : ∀ q : ℚ, character (algebraMap ℚ AQ q) = 1
  character_real : ∀ t : ℝ, character (t, 0) = standardRealCharacter t
  finiteCharacter : AddChar AQf ℂ
  finiteCharacter_eq : ∀ t, finiteCharacter t = character (0, t)
  finiteMeasure : Measure (ι → AQf)
  finiteMeasure_haar : finiteMeasure.IsAddHaarMeasure
  finiteMeasure_selfDual : ∀ (φ : finiteSchwartz ι) x,
    fourier finiteCharacter finiteMeasure
      (fourier finiteCharacter finiteMeasure φ.val) x = φ.val (-x)
  real : SchrodingerCover ℝ standardRealCharacter volume (realSchwartz ι) MpR
  finite : SchrodingerCover AQf finiteCharacter finiteMeasure (finiteSchwartz ι) MpF
  adelic : SchrodingerCover AQ character (adelicMeasure finiteMeasure)
    (adelicSchwartz ι) MpA
  includeReal : MpR →* MpA
  includeFinite : MpF →* MpA
  commute : ∀ r f, Commute (includeReal r) (includeFinite f)
  factorization : ∀ (r : MpR) (f : MpF) (h : realSchwartz ι) (φ : finiteSchwartz ι),
    adelic.action (includeReal r * includeFinite f) (tensor h φ) =
      tensor (real.action r h) (finite.action f φ)
  includeReal_covers : ∀ r,
    (adelic.project (includeReal r)).val = fun i j =>
      ((real.project r).val i j,
        (1 : Matrix (Sum ι ι) (Sum ι ι) AQf) i j)
  includeFinite_covers : ∀ f,
    (adelic.project (includeFinite f)).val = fun i j =>
      ((1 : Matrix (Sum ι ι) (Sum ι ι) ℝ) i j,
        (finite.project f).val i j)
  centralProduct_kernel : ∀ r f,
    includeReal r * includeFinite f = 1 ↔
      (r = 1 ∧ f = 1) ∨ (r = real.negOne ∧ f = finite.negOne)
  -- Exactness of the real/finite central-product presentation.
  decompose : ∀ (a : MpA) (r : MpR),
    mapSp (RingHom.fst ℝ AQf) (adelic.project a) = real.project r →
    ∃ f : MpF, includeReal r * includeFinite f = a
  rationalSplit : Sp ι ℚ →* MpA
  rationalSplit_covers : ∀ γ,
    adelic.project (rationalSplit γ) = mapSp (algebraMap ℚ AQ) γ
  -- The global generator laws fix the rational splitting's scalar.
  rational_linear : ∀ (γ : Sp ι ℚ) (A : (Matrix ι ι ℚ)ˣ),
    γ.val = Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose →
    ∀ (f : adelicSchwartz ι) x,
      (adelic.action (rationalSplit γ) f).val x =
        f.val ((A.val.transpose.map (algebraMap ℚ AQ)) *ᵥ x)
  rational_quadratic : ∀ (γ : Sp ι ℚ) (B : Matrix ι ι ℚ),
    B.IsSymm → γ.val = Matrix.fromBlocks 1 B 0 1 →
    ∀ (f : adelicSchwartz ι) x,
      (adelic.action (rationalSplit γ) f).val x =
        character (algebraMap ℚ AQ (1 / 2) *
          (x ⬝ᵥ (B.map (algebraMap ℚ AQ) *ᵥ x))) * f.val x
  rational_fourier : ∀ γ : Sp ι ℚ,
    γ.val = Matrix.fromBlocks 0 (-1) 1 0 →
    ∀ (f : adelicSchwartz ι) x,
      (adelic.action (rationalSplit γ) f).val x =
        fourier character (adelicMeasure finiteMeasure) f.val x
  vacuum : realSchwartz ι
  vacuum_eq : ∀ x, vacuum.val x =
    Complex.exp (-((Real.pi : ℂ) * ∑ i, (x i : ℂ) ^ 2))
  real_normalization : ∀ r : MpR,
    ((real.action r vacuum).val 0) ^ 2 =
      (denominatorDet (blocks (real.project r)) (basePeriod ι))⁻¹

namespace WeilData

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : WeilData ι MpR MpF MpA)

def rationalAction : Sp ι ℚ →*
    (adelicSchwartz ι ≃ₗ[ℂ] adelicSchwartz ι) :=
  D.adelic.action.comp D.rationalSplit

/-- The real sign is chosen by the previously constructed branch at `i I`.
Only a single vacuum matrix coefficient is used, not a theta identity. -/
theorem exists_normalizedRealLift (γ : Sp ι ℚ) :
    ∃ r : MpR, D.real.project r = mapSp (algebraMap ℚ ℝ) γ ∧
      (D.real.action r D.vacuum).val 0 =
        (halfDet (realBlocks γ) (toSiegel (basePeriod ι)))⁻¹ := by
  obtain ⟨r, hr⟩ := D.real.surjective (mapSp (algebraMap ℚ ℝ) γ)
  have hs : ((D.real.action r D.vacuum).val 0) ^ 2 =
      ((halfDet (realBlocks γ) (toSiegel (basePeriod ι)))⁻¹) ^ 2 := by
    rw [D.real_normalization, hr, inv_pow, halfDet_sq]
    rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact ⟨r, hr, h⟩
  · refine ⟨D.real.negOne * r, ?_, ?_⟩
    · rw [map_mul, D.real.project_negOne, one_mul, hr]
    · rw [map_mul]
      change (D.real.action D.real.negOne (D.real.action r D.vacuum)).val 0 = _
      rw [D.real.genuine]
      change -((D.real.action r D.vacuum).val 0) = _
      rw [h, neg_neg]

def normalizedRealLift (γ : Sp ι ℚ) : MpR :=
  (D.exists_normalizedRealLift γ).choose

theorem normalizedRealLift_covers (γ : Sp ι ℚ) :
    D.real.project (D.normalizedRealLift γ) = mapSp (algebraMap ℚ ℝ) γ :=
  (D.exists_normalizedRealLift γ).choose_spec.1

theorem normalizedRealLift_coefficient (γ : Sp ι ℚ) :
    (D.real.action (D.normalizedRealLift γ) D.vacuum).val 0 =
      (halfDet (realBlocks γ) (toSiegel (basePeriod ι)))⁻¹ :=
  (D.exists_normalizedRealLift γ).choose_spec.2

theorem normalizedRealLift_unique (γ : Sp ι ℚ) (r : MpR)
    (hr : D.real.project r = mapSp (algebraMap ℚ ℝ) γ)
    (hcoef : (D.real.action r D.vacuum).val 0 =
      (halfDet (realBlocks γ) (toSiegel (basePeriod ι)))⁻¹) :
    r = D.normalizedRealLift γ := by
  have hker : D.real.project (r * (D.normalizedRealLift γ)⁻¹) = 1 := by
    rw [map_mul, map_inv, hr, D.normalizedRealLift_covers, mul_inv_cancel]
  rcases (D.real.kernel _).mp hker with h | h
  · exact mul_inv_eq_one.mp h
  · have hrel : r = D.real.negOne * D.normalizedRealLift γ :=
      mul_inv_eq_iff_eq_mul.mp h
    rw [hrel, map_mul] at hcoef
    change (D.real.action D.real.negOne
      (D.real.action (D.normalizedRealLift γ) D.vacuum)).val 0 = _ at hcoef
    rw [D.real.genuine] at hcoef
    change -((D.real.action (D.normalizedRealLift γ) D.vacuum).val 0) = _ at hcoef
    rw [D.normalizedRealLift_coefficient] at hcoef
    have hz : (2 : ℂ) *
        (halfDet (realBlocks γ) (toSiegel (basePeriod ι)))⁻¹ = 0 := by
      linear_combination -hcoef
    exact (mul_ne_zero (by norm_num)
      (inv_ne_zero (halfDet_ne_zero _ _)) hz).elim

theorem rationalSplit_realProjection (γ : Sp ι ℚ) :
    mapSp (RingHom.fst ℝ AQf) (D.adelic.project (D.rationalSplit γ)) =
      mapSp (algebraMap ℚ ℝ) γ := by
  rw [D.rationalSplit_covers]
  apply Subtype.ext
  ext i j
  rfl

theorem exists_finiteLift (γ : Sp ι ℚ) :
    ∃ f : MpF,
      D.includeReal (D.normalizedRealLift γ) * D.includeFinite f =
        D.rationalSplit γ := by
  apply D.decompose
  rw [D.rationalSplit_realProjection, D.normalizedRealLift_covers]

def finiteLift (γ : Sp ι ℚ) : MpF := (D.exists_finiteLift γ).choose

theorem finiteLift_factorization (γ : Sp ι ℚ) :
    D.includeReal (D.normalizedRealLift γ) * D.includeFinite (D.finiteLift γ) =
      D.rationalSplit γ :=
  (D.exists_finiteLift γ).choose_spec

def finiteAction (γ : Sp ι ℚ) : finiteSchwartz ι ≃ₗ[ℂ] finiteSchwartz ι :=
  D.finite.action (D.finiteLift γ)

theorem rationalAction_tensor (γ : Sp ι ℚ)
    (f : realSchwartz ι) (φ : finiteSchwartz ι) :
    D.rationalAction γ (tensor f φ) =
      tensor (D.real.action (D.normalizedRealLift γ) f) (D.finiteAction γ φ) := by
  change D.adelic.action (D.rationalSplit γ) (tensor f φ) = _
  rw [← D.finiteLift_factorization γ]
  exact D.factorization _ _ f φ

theorem includeFinite_injective : Function.Injective D.includeFinite := by
  intro f h heq
  have hker : D.includeReal 1 * D.includeFinite (f⁻¹ * h) = 1 := by
    simp [map_mul, heq]
  rcases (D.centralProduct_kernel 1 (f⁻¹ * h)).mp hker with h | h
  · exact inv_mul_eq_one.mp h.2
  · exact (D.real.negOne_ne_one h.1.symm).elim

theorem finiteLift_unique (γ : Sp ι ℚ) (f : MpF)
    (hf : D.includeReal (D.normalizedRealLift γ) * D.includeFinite f =
      D.rationalSplit γ) : f = D.finiteLift γ := by
  apply D.includeFinite_injective
  exact mul_left_cancel (hf.trans (D.finiteLift_factorization γ).symm)

theorem finiteLift_covers (γ : Sp ι ℚ) :
    D.finite.project (D.finiteLift γ) = mapSp (algebraMap ℚ AQf) γ := by
  have h := congrArg
    (fun a => mapSp (RingHom.snd ℝ AQf) (D.adelic.project a))
    (D.finiteLift_factorization γ)
  have hR : mapSp (RingHom.snd ℝ AQf)
      (D.adelic.project (D.includeReal (D.normalizedRealLift γ))) = 1 := by
    apply Subtype.ext
    change (D.adelic.project (D.includeReal (D.normalizedRealLift γ))).val.map
      (RingHom.snd ℝ AQf) = 1
    rw [D.includeReal_covers]
    rfl
  have hF : mapSp (RingHom.snd ℝ AQf)
      (D.adelic.project (D.includeFinite (D.finiteLift γ))) =
      D.finite.project (D.finiteLift γ) := by
    apply Subtype.ext
    change (D.adelic.project (D.includeFinite (D.finiteLift γ))).val.map
      (RingHom.snd ℝ AQf) = _
    rw [D.includeFinite_covers]
    rfl
  have hQ : mapSp (RingHom.snd ℝ AQf)
      (D.adelic.project (D.rationalSplit γ)) = mapSp (algebraMap ℚ AQf) γ := by
    rw [D.rationalSplit_covers]
    apply Subtype.ext
    ext i j
    rfl
  simpa only [map_mul, hR, hF, one_mul, hQ] using h

end WeilData

def diagonal (x : ι → ℚ) : ι → AQ := fun i => algebraMap ℚ AQ (x i)
def finiteDiagonal (x : ι → ℚ) : ι → AQf := fun i => algebraMap ℚ AQf (x i)

def thetaFunctional (f : adelicSchwartz ι) : ℂ :=
  ∑' x : ι → ℚ, f.val (PoissonAutomorphyNormalizationData.diagonal x)

def thetaTerm (φ : finiteSchwartz ι)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℚ) : ℂ :=
  φ.val (finiteDiagonal x) * Complex.exp
    ((Real.pi : ℂ) * Complex.I *
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.matrix (fun i => (x i : ℝ)) (fun i => (x i : ℝ)) +
      (2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (x i : ℂ) * z i)

def theta (φ : finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : ℂ :=
  ∑' x : ι → ℚ, thetaTerm φ Z z x

end RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

namespace RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
section

/-! Concrete properties of the test spaces used by PoissonAutomorphy. -/

variable {ι : Type*} [Fintype ι]

theorem finiteSchwartz_mem_iff (f : (ι → AQf) → ℂ) :
    f ∈ finiteSchwartz ι ↔ IsLocallyConstant f ∧ HasCompactSupport f := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact hf
    | zero => exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
    | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
    | smul c f _ hf =>
      exact ⟨hf.1.comp (fun z : ℂ => c * z), hf.2.smul_left⟩
  · intro hf
    exact Submodule.subset_span hf

theorem realSchwartz_mem_iff (f : (ι → ℝ) → ℂ) :
    f ∈ realSchwartz ι ↔ ∃ φ : SchwartzMap (ι → ℝ) ℂ, f = φ := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact hf
    | zero => exact ⟨0, rfl⟩
    | add f g _ _ hf hg =>
      obtain ⟨φ, rfl⟩ := hf
      obtain ⟨ψ, rfl⟩ := hg
      exact ⟨φ + ψ, rfl⟩
    | smul c f _ hf =>
      obtain ⟨φ, rfl⟩ := hf
      exact ⟨c • φ, rfl⟩
  · intro hf
    exact Submodule.subset_span hf

theorem finiteSchwartz_continuous (φ : finiteSchwartz ι) : Continuous φ.val :=
  ((finiteSchwartz_mem_iff φ.val).mp φ.property).1.continuous

theorem finiteSchwartz_hasCompactSupport (φ : finiteSchwartz ι) :
    HasCompactSupport φ.val :=
  ((finiteSchwartz_mem_iff φ.val).mp φ.property).2

theorem finiteSchwartz_bounded (φ : finiteSchwartz ι) :
    ∃ C : ℝ, ∀ x, ‖φ.val x‖ ≤ C :=
  (finiteSchwartz_hasCompactSupport φ).exists_bound_of_continuous
    (finiteSchwartz_continuous φ)

end

section

/-! Absolute convergence of Schwartz restrictions to discrete lattices. -/

open scoped Classical
open Filter OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem schwartz_lattice_summable (L : Submodule ℤ V) [DiscreteTopology L]
    (f : SchwartzMap V ℂ) : Summable (fun x : L => ‖f x.val‖) := by
  have hclosed : IsClosed (L : Set V) :=
    @AddSubgroup.isClosed_of_discreteTopology _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hproper : Tendsto (Subtype.val : L → V) cofinite (cocompact V) :=
    hclosed.tendsto_coe_cofinite_of_isDiscrete DiscreteTopology.isDiscrete
  let r : ℝ := -(Module.finrank ℤ L : ℝ) - 1
  have hr : r < -(Module.finrank ℤ L : ℝ) := by dsimp [r]; linarith
  exact summable_of_isBigO (ZLattice.summable_norm_rpow L r hr)
    ((f.isBigO_cocompact_rpow r).norm_left.comp_tendsto hproper)

variable {ι : Type*} [Fintype ι]

def rationalReal (x : ι → ℚ) : ι → ℝ := fun i => (x i : ℝ)

omit [Fintype ι] in
theorem rationalReal_injective : Function.Injective (rationalReal (ι := ι)) := by
  intro x y h
  funext i
  have hi : (x i : ℝ) = (y i : ℝ) := congrFun h i
  exact_mod_cast hi

def scaleMap (n : ℤ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (n : ℝ) • ContinuousLinearMap.id ℝ (ι → ℝ)

def scaledLattice (n : ℤ) : Submodule ℤ (ι → ℝ) :=
  ZLattice.comap ℝ (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (scaleMap (ι := ι) n).toLinearMap

theorem scaledLattice_discrete (n : ℤ) (hn : n ≠ 0) :
    DiscreteTopology (scaledLattice (ι := ι) n) := by
  apply ZLattice.comap_discreteTopology ℝ (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι)
    (scaleMap n).continuous
  intro x y h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  change (n : ℝ) • x = (n : ℝ) • y at h
  have heq := congrArg (fun z : ι → ℝ => (n : ℝ)⁻¹ • z) h
  simpa only [smul_smul, inv_mul_cancel₀ hn', one_smul] using heq

theorem rationalReal_mem_scaledLattice (n : ℤ) (x : ι → ℚ)
    (hx : ∀ i, ∃ m : ℤ, (m : ℚ) = (n : ℚ) * x i) :
    rationalReal x ∈ scaledLattice n := by
  change (scaleMap n (rationalReal x)) ∈ AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι
  apply ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ _).mpr
  intro i
  obtain ⟨m, hm⟩ := hx i
  refine ⟨m, ?_⟩
  have hreal := congrArg (fun q : ℚ => (q : ℝ)) hm
  simpa [scaleMap, rationalReal] using hreal

end

/-! Locally uniform absolute convergence of Schwartz lattice periodization. -/

open scoped Classical
open Filter _root_.TopologicalSpace Asymptotics

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem schwartz_one_add_bound (f : SchwartzMap V ℂ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ k * ‖f x‖ ≤ C := by
  let C := 2 ^ k * (Finset.Iic (k, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  refine ⟨max 0 C, le_max_left _ _, fun x => ?_⟩
  apply le_trans _ (le_max_right _ _)
  simpa only [norm_iteratedFDeriv_zero] using
    f.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
      le_rfl le_rfl x

def shiftedSchwartz (f : SchwartzMap V ℂ) (a : V) : C(V, ℂ) :=
  ⟨fun x => f (x + a), f.continuous.comp (continuous_id.add continuous_const)⟩

theorem schwartz_lattice_locally_summable_norm (L : Submodule ℤ V) [DiscreteTopology L]
    (f : SchwartzMap V ℂ) (K : Compacts V) :
    Summable (fun a : L => ‖(shiftedSchwartz f a.val).restrict K‖) := by
  let k := Module.finrank ℤ L + 1
  obtain ⟨C, hC, hf⟩ := schwartz_one_add_bound f k
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  let S := max 0 R
  have hS : 0 ≤ S := le_max_left _ _
  have hxS : ∀ x : K, ‖x.val‖ ≤ S := by
    intro x
    have h := hR x.property
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_right _ _)
  have hbound : ∀ (a : L), a ≠ 0 → ∀ x : K,
      ‖f (x.val + a.val)‖ ≤ (1 + S) ^ k * C * ‖a.val‖ ^ (-(k : ℝ)) := by
    intro a ha x
    have ha0 : 0 < ‖a.val‖ := norm_pos_iff.mpr (fun h => ha (Subtype.ext h))
    have htri : ‖a.val‖ ≤ ‖x.val + a.val‖ + ‖x.val‖ := by
      calc
        ‖a.val‖ = ‖(x.val + a.val) - x.val‖ := by congr 1; abel
        _ ≤ ‖x.val + a.val‖ + ‖x.val‖ := norm_sub_le _ _
    have hbase : ‖a.val‖ ≤ (1 + S) * (1 + ‖x.val + a.val‖) := by
      nlinarith [hxS x, norm_nonneg (x.val + a.val)]
    have hweight : ‖a.val‖ ^ k * ‖f (x.val + a.val)‖ ≤ (1 + S) ^ k * C := by
      calc
        _ ≤ ((1 + S) * (1 + ‖x.val + a.val‖)) ^ k * ‖f (x.val + a.val)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hbase k) (norm_nonneg _)
        _ = (1 + S) ^ k * ((1 + ‖x.val + a.val‖) ^ k * ‖f (x.val + a.val)‖) := by
          rw [mul_pow, mul_assoc]
        _ ≤ (1 + S) ^ k * C := mul_le_mul_of_nonneg_left (hf _) (by positivity)
    rw [Real.rpow_neg ha0.le, Real.rpow_natCast, ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos ha0 k)).mpr (by simpa only [mul_comm] using hweight)
  have hr : -(k : ℝ) < -(Module.finrank ℤ L : ℝ) := by
    dsimp [k]
    push_cast
    linarith
  apply summable_of_isBigO (ZLattice.summable_norm_rpow L (-(k : ℝ)) hr)
  refine IsBigO.of_bound ((1 + S) ^ k * C) ?_
  filter_upwards [eventually_cofinite_ne (0 : L)] with a ha
  rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  exact hbound a ha

def latticePeriodization (L : Submodule ℤ V) [DiscreteTopology L]
    (f : SchwartzMap V ℂ) : C(V, ℂ) := ∑' a : L, shiftedSchwartz f a.val

theorem latticePeriodization_apply (L : Submodule ℤ V) [DiscreteTopology L]
    (f : SchwartzMap V ℂ) (x : V) :
    latticePeriodization L f x = ∑' a : L, f (x + a.val) := by
  exact (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
    (schwartz_lattice_locally_summable_norm L f)) x).symm

theorem latticePeriodization_add (L : Submodule ℤ V) [DiscreteTopology L]
    (f : SchwartzMap V ℂ) (a : L) (x : V) :
    latticePeriodization L f (x + a.val) = latticePeriodization L f x := by
  simp only [latticePeriodization_apply]
  have h := (Equiv.addLeft a).tsum_eq (fun b : L => f (x + b.val))
  simpa only [Equiv.coe_addLeft, Submodule.coe_add, add_assoc] using h

end RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction

end

end OAI
