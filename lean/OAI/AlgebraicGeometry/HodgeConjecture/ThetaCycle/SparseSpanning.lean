import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Projection
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Sparse Spanning -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SparseSpanning.CM

noncomputable section

section

/-! Genuine compactly supported locally constant finite-adelic inputs for
the sparse lattice cosets used in theta-gradient spanning. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

variable {ι : Type*} [Fintype ι]

def finiteLatticeInput (q : ℚ) (hq : q ≠ 0) : HeckeCycles.GeometricSource.CM.FiniteInput ι := by
  refine ⟨(RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := ι) q hq : Set (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)).indicator (fun _ => 1), ?_, ?_⟩
  · exact ((LocallyConstant.const (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (1 : ℂ)).indicator
      ⟨(RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact q hq).isClosed, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isOpen q hq⟩).isLocallyConstant
  · apply (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact q hq).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact q hq).isClosed
    exact Set.support_indicator_subset

def finiteCosetInput (q : ℚ) (hq : q ≠ 0) (a : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : HeckeCycles.GeometricSource.CM.FiniteInput ι :=
  ⟨(finiteLatticeInput q hq).val ∘ Homeomorph.addRight (-a),
    (finiteLatticeInput q hq).property.1.comp_continuous (Homeomorph.addRight (-a)).continuous,
    (finiteLatticeInput q hq).property.2.comp_homeomorph (Homeomorph.addRight (-a))⟩

omit [Fintype ι] in
theorem rational_coset_membership (q : ℚ) (hq : q ≠ 0) (a x : ι → ℚ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x - RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔
      ∃ m : ι → ℤ, ∀ i, x i = a i + q * (m i : ℚ) := by
  rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff]
  change (∀ i, algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q⁻¹ *
    (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (x i) - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (a i)) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) ↔ _
  simp only [← map_sub, ← map_mul, RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff]
  constructor
  · intro h
    choose m hm using h
    refine ⟨m, fun i => ?_⟩
    rw [hm i, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
    ring
  · rintro ⟨m, hm⟩ i
    refine ⟨m i, ?_⟩
    rw [hm i, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

theorem coordinate_lattice_integral (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) :
    ∀ i, ∃ m : ℤ, (m : ℝ) = (a : ι → ℝ) i := by
  exact ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ (a : ι → ℝ)).mp a.property

def latticeRational (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) : ι → ℚ :=
  fun i => ((coordinate_lattice_integral a i).choose : ℚ)

theorem latticeRational_real (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (i : ι) :
    (latticeRational a i : ℝ) = (a : ι → ℝ) i := by
  simpa only [latticeRational, Rat.cast_intCast] using (coordinate_lattice_integral a i).choose_spec

def sparseFiniteInput (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) : HeckeCycles.GeometricSource.CM.FiniteInput ι :=
  finiteCosetInput (n + 1 : ℚ) (by positivity) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational a))

theorem sparse_input_lattice_values (a x : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) :
    (sparseFiniteInput a n).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational x)) =
      if ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) n a x then 1 else 0 := by
  have he : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational x) - RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational a) ∈
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (n + 1 : ℚ) (by positivity) ↔
      ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) n a x := by
    rw [rational_coset_membership]
    constructor
    · rintro ⟨m, hm⟩
      have hmem : (fun i => (m i : ℝ)) ∈ ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι :=
        ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ _).mpr (fun i => ⟨m i, rfl⟩)
      refine ⟨⟨fun i => (m i : ℝ), hmem⟩, ?_⟩
      apply Subtype.ext
      funext i
      have hi := congrArg (fun q : ℚ => (q : ℝ)) (hm i)
      simpa [latticeRational_real, Nat.cast_add, Nat.cast_one] using hi
    · rintro ⟨l, hl⟩
      refine ⟨fun i => (coordinate_lattice_integral l i).choose, fun i => ?_⟩
      apply Rat.cast_injective (α := ℝ)
      have hi := congrFun (congrArg Subtype.val hl) i
      push_cast
      rw [latticeRational_real, latticeRational_real, (coordinate_lattice_integral l i).choose_spec]
      simpa using hi
  change (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := ι) (n + 1 : ℚ) _ : Set (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)).indicator (fun _ => (1 : ℂ))
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational x) + -RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational a)) = _
  simp only [← sub_eq_add_neg, Set.indicator_apply, SetLike.mem_coe, he]

end

section

/-! The actual finite coset input is supported, on rational points,
on the standard integral position lattice. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

variable {ι : Type*} [Fintype ι]

theorem realPosition_latticeRational (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) :
    RepresentationTheory.Theta.DerivativeFactorizationDefinitions.realPosition (latticeRational a) = (a : ι → ℝ) := by
  funext i
  exact latticeRational_real a i

theorem latticeRational_injective : Function.Injective (latticeRational (ι := ι)) := by
  intro a b hab
  apply Subtype.ext
  rw [← realPosition_latticeRational a, ← realPosition_latticeRational b, hab]

theorem sparse_input_rational_support (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ)
    (x : ι → ℚ) (hx : (sparseFiniteInput a n).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) ≠ 0) :
    x ∈ Set.range (latticeRational (ι := ι)) := by
  have hm : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x - RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational a) ∈
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (n + 1 : ℚ) (by positivity) := by
    by_contra hn
    apply hx
    change (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := ι) (n + 1 : ℚ) _ : Set (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)).indicator
      (fun _ => (1 : ℂ)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x + -RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational a)) = 0
    exact Set.indicator_of_notMem (by simpa only [← sub_eq_add_neg, SetLike.mem_coe] using hn) _
  obtain ⟨m, hm⟩ := (rational_coset_membership _ (by positivity) _ _).mp hm
  have hint (i : ι) : ∃ k : ℤ, (k : ℚ) = x i := by
    refine ⟨(coordinate_lattice_integral a i).choose + (n + 1) * m i, ?_⟩
    rw [hm i]
    simp [latticeRational]
  have hL : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.realPosition x ∈ ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι := by
    apply ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ _).mpr
    intro i
    obtain ⟨k, hk⟩ := hint i
    refine ⟨k, ?_⟩
    change (k : ℝ) = (x i : ℝ)
    exact_mod_cast hk
  refine ⟨⟨RepresentationTheory.Theta.DerivativeFactorizationDefinitions.realPosition x, hL⟩, ?_⟩
  apply RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice.realPosition_injective
  exact realPosition_latticeRational _

end

section

/-! The literal finite-adelic theta derivatives span the full Jacobi
cotangent space. The sparse-input realization is proved term by term. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Weil.CM

variable {ι : Type*} [Fintype ι]

theorem sparse_first_coefficient (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) :
    RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient (sparseFiniteInput a n) Z.matrix =
      Z.phase.sparseThetaGradient (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) a n := by
  let φ := sparseFiniteInput a n
  let f := fun x : ι → ℚ => φ.val (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal x) •
    ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.realPosition x)
      (ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.matrix)
  have hs : Function.support f ⊆ Set.range (latticeRational (ι := ι)) := by
    intro x hx
    apply sparse_input_rational_support a n x
    intro hzero
    apply hx
    change φ.val (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal x) • _ = 0
    change φ.val (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal x) = 0 at hzero
    rw [hzero]
    ext v
    simp
  change (∑' x, f x) = _
  rw [← latticeRational_injective.tsum_eq hs, ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.sparseThetaGradient_eq]
  unfold ComplexMultiplication.SparseLatticeSums.CM.sparseLatticeSum
  apply tsum_congr
  intro x
  have hv := sparse_input_lattice_values a x n
  change φ.val (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal (latticeRational x)) = _ at hv
  change φ.val (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal (latticeRational x)) •
    ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι)
      (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.realPosition (latticeRational x)) (ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.matrix) = _
  rw [hv, realPosition_latticeRational]
  split_ifs
  · simp [ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm, ComplexMultiplication.SparseGaussianSpanning.CM.weightedLatticeLinearTerm, ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.gaussianWeight,
      ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase]
  · ext v
    simp

theorem sparse_source_first (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) :
    fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries (sparseFiniteInput a n) Z) 0 =
      Z.phase.sparseThetaGradient (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) a n := by
  rw [HeckeCycles.Theta.Weil.CM.source_first_is_canonical]
  exact sparse_first_coefficient Z a n

theorem source_first_span_eq_top (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    Submodule.span ℂ (Set.range (fun φ : HeckeCycles.GeometricSource.CM.FiniteInput ι =>
      fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ Z) 0)) = ⊤ := by
  apply top_unique
  rw [← ComplexMultiplication.ThetaCoordinates.CM.span_coordinate_sparseThetaGradients_eq_top ι Z.phase]
  apply Submodule.span_mono
  rintro l ⟨⟨a, n⟩, rfl⟩
  exact ⟨sparseFiniteInput a n, sparse_source_first Z a n⟩

end

/-! The actual projected theta one-forms span every ball cotangent.
Both the finite inputs and the projection's surjectivity are constructed. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

def jacobiCoefficients (ι : Type*) [Fintype ι] :
    ((ι → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun l j := l (Pi.single j 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem jacobi_coefficients_surjective (ι : Type*) [Fintype ι] :
    Function.Surjective (jacobiCoefficients ι) := by
  intro c
  refine ⟨∑ j, c j • (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ), ?_⟩
  funext i
  simp [jacobiCoefficients, Pi.single_apply]

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}

def graphCotangentLinear (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    (HeckeCycles.GeometricSource.CM.Positions K places → ℂ) →ₗ[ℂ] (HeckeCycles.GeometricSource.CM.BallChart →L[ℂ] ℂ) where
  toFun := Projection.CM.graphCotangent K L z
  map_add' x y := by
    ext ξ
    simp [Projection.CM.graphCotangent, map_add, mul_add, add_mul]
    ring
  map_smul' c x := by
    ext ξ
    simp [Projection.CM.graphCotangent, map_smul, mul_assoc]
    ring

def thetaCotangentProjection (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    ((HeckeCycles.GeometricSource.CM.Positions K places → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (HeckeCycles.GeometricSource.CM.BallChart →L[ℂ] ℂ) :=
  (graphCotangentLinear K L z).comp (jacobiCoefficients (HeckeCycles.GeometricSource.CM.Positions K places))

theorem theta_cotangent_projection_surjective (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    Function.Surjective (thetaCotangentProjection K L z) :=
  (Projection.CM.graph_cotangent_surjective K L z hz).comp (jacobi_coefficients_surjective (HeckeCycles.GeometricSource.CM.Positions K places))

omit [IsGalois ℚ K] in
theorem source_covector_eq_projection (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    Projection.CM.sourceThetaCovector K L φ z =
      thetaCotangentProjection K L z (fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0) := by
  rw [Projection.CM.source_covector_graph_projection]
  dsimp only [thetaCotangentProjection, LinearMap.comp_apply,
    graphCotangentLinear, jacobiCoefficients]
  apply congrArg (Projection.CM.graphCotangent K L z)
  funext j
  apply congrArg (fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0)
  funext k
  simp only [Pi.single_apply]
  split_ifs <;> rfl

theorem source_theta_covector_span (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    Submodule.span ℂ (Set.range (fun φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places) =>
      Projection.CM.sourceThetaCovector K L φ z)) = ⊤ := by
  simp_rw [source_covector_eq_projection]
  rw [Set.range_comp' (thetaCotangentProjection K L z), Submodule.span_image,
    source_first_span_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (theta_cotangent_projection_surjective K L z hz)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SparseSpanning.CM
