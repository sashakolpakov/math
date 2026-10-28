import OAI.RepresentationTheory.Theta.Intrinsic
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # One Forms Intrinsic Lattice -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.OneFormsIntrinsicLattice.Intrinsic

/-! The integral position lattice in the actual rational Schrödinger coordinates. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Intrinsic.OneFormsIntrinsic

variable {F : Type} [Field F] [NumberField F] {N : ℕ}
variable {ι : Type}

def integerPosition : (Fin N → 𝓞 F) →ₗ[ℤ] (Fin N → F) where
  toFun r i := r i
  map_add' _ _ := by funext i; exact map_add _ _ _
  map_smul' _ _ := by funext i; simp

def realCoordinates (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ)) :
    (Fin N → F) →ₗ[ℚ] (ι → ℝ) where
  toFun x i := (e x i : ℝ)
  map_add' x y := by funext i; simp
  map_smul' c x := by
    funext i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Rat.cast_mul]
    exact (Rat.cast_smul_eq_qsmul ℝ c (e x i : ℝ)).symm

theorem realCoordinates_injective (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ)) :
    Function.Injective (realCoordinates e) := by
  intro x y h
  apply e.injective
  funext i
  exact Rat.cast_injective (congrFun h i)

def integerCoordinates (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ)) :
    (Fin N → 𝓞 F) →ₗ[ℤ] (ι → ℝ) :=
  ((realCoordinates e).restrictScalars ℤ).comp integerPosition

def integralLattice (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ)) :
    Submodule ℤ (ι → ℝ) := (integerCoordinates e).range

def latticePosition (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ))
    (x : integralLattice e) : Fin N → F :=
  (integerPosition (F := F)) x.property.choose

theorem latticePosition_coordinates (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ))
    (x : integralLattice e) : realCoordinates e (latticePosition e x) = x.val :=
  x.property.choose_spec

theorem latticePosition_injective (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ)) :
    Function.Injective (latticePosition e) := by
  intro x y h
  apply Subtype.ext
  rw [← latticePosition_coordinates e x, ← latticePosition_coordinates e y, h]

theorem latticePosition_range (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ))
    (x : Fin N → F) :
    x ∈ Set.range (latticePosition e) ↔ realCoordinates e x ∈ integralLattice e := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [latticePosition_coordinates]
    exact a.property
  · intro hx
    refine ⟨⟨realCoordinates e x, hx⟩, ?_⟩
    apply realCoordinates_injective e
    exact latticePosition_coordinates e _

theorem latticePosition_integer (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ))
    (x : integralLattice e) : ∃ r : Fin N → 𝓞 F, (integerPosition (F := F)) r = latticePosition e x :=
  ⟨x.property.choose, rfl⟩

theorem sparse_coordinates_iff [Fintype ι] (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ))
    (a x : integralLattice e) (n : ℕ) :
    (∃ r : Fin N → 𝓞 F,
      latticePosition e x = latticePosition e a + (n + 1 : F) • (integerPosition (F := F)) r) ↔
      AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset (integralLattice e) n a x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨⟨integerCoordinates e r, LinearMap.mem_range_self _ r⟩, ?_⟩
    apply Subtype.ext
    have h := congrArg (realCoordinates e) hr
    rw [latticePosition_coordinates, map_add, latticePosition_coordinates] at h
    have hs : (n + 1 : F) • (integerPosition (F := F)) r = (n + 1) • (integerPosition (F := F)) r := by
      ext i
      simp [nsmul_eq_mul]
    rw [hs, map_nsmul] at h
    exact h
  · rintro ⟨r, hr⟩
    obtain ⟨r₀, hr₀⟩ := latticePosition_integer e r
    refine ⟨r₀, ?_⟩
    apply realCoordinates_injective e
    rw [map_add, latticePosition_coordinates, latticePosition_coordinates]
    have hs : (n + 1 : F) • (integerPosition (F := F)) r₀ = (n + 1) • (integerPosition (F := F)) r₀ := by
      ext i
      simp [nsmul_eq_mul]
    rw [hs, map_nsmul, hr₀, latticePosition_coordinates]
    exact congrArg Subtype.val hr

theorem integerPosition_span :
    Submodule.span ℚ (Set.range (integerPosition (F := F) (N := N))) = ⊤ := by
  let S := Submodule.span ℚ (Set.range (integerPosition (F := F) (N := N)))
  have hsingle (i : Fin N) (x : F) : Pi.single i x ∈ S := by
    have hle : Submodule.span ℚ (Set.range (NumberField.integralBasis F)) ≤
        S.comap (LinearMap.single ℚ (fun _ : Fin N => F) i) := by
      apply Submodule.span_le.mpr
      rintro y ⟨j, rfl⟩
      apply Submodule.subset_span
      refine ⟨Pi.single i (NumberField.RingOfIntegers.basis F j), ?_⟩
      funext k
      by_cases hki : k = i <;>
        simp [integerPosition, NumberField.integralBasis_apply, hki]
    apply hle
    rw [(NumberField.integralBasis F).span_eq]
    trivial
  apply top_unique
  intro x _
  have hx : (∑ i : Fin N, Pi.single i (x i)) = x := by
    funext i
    simp
  rw [← hx]
  exact Submodule.sum_mem S (fun i _ => hsingle i (x i))

section Spanning
variable [Fintype ι]

/-- Integral F-positions span the entire complex Jacobi cotangent after
any rational coordinate equivalence. -/
theorem integralLattice_pairing_span
    (e : (Fin N → F) ≃ₗ[ℚ] (ι → ℚ)) :
    Submodule.span ℂ (Set.range (fun x : integralLattice e =>
      AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι x.val)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun x : integralLattice e =>
    AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι x.val))
  let T : (Fin N → F) →ₗ[ℚ] ((ι → ℂ) →L[ℂ] ℂ) :=
    ((AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι).toLinearMap.restrictScalars ℚ).comp (realCoordinates e)
  have hall (x : Fin N → F) : T x ∈ S := by
    have hle : Submodule.span ℚ (Set.range (integerPosition (F := F) (N := N))) ≤
        (S.restrictScalars ℚ).comap T := by
      apply Submodule.span_le.mpr
      rintro y ⟨r, rfl⟩
      exact Submodule.subset_span
        ⟨⟨integerCoordinates e r, LinearMap.mem_range_self _ r⟩, rfl⟩
    rw [integerPosition_span] at hle
    exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℚ (Fin N → F)))
  have hproj (i : ι) : (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ) ∈ S := by
    have h := hall (e.symm (Pi.single i 1))
    change AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι (realCoordinates e (e.symm (Pi.single i 1))) ∈ S at h
    have he : realCoordinates e (e.symm (Pi.single i 1)) = (Pi.basisFun ℝ ι) i := by
      funext j
      by_cases hji : j = i <;> simp [realCoordinates, Pi.basisFun_apply, hji]
    rw [he, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_basis] at h
    exact h
  apply top_unique
  intro l _
  have he : l = ∑ i : ι, l (Pi.single i 1) •
      (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ) := by
    ext z
    have hz : z = ∑ i : ι, z i • Pi.single i (1 : ℂ) := by
      funext j
      simp [Pi.single_apply]
    conv_lhs => rw [hz]
    simp [mul_comm]
  rw [he]
  exact Submodule.sum_mem S (fun i _ => S.smul_mem _ (hproj i))

end Spanning

variable {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

/-- Discreteness is a consequence of AdelicTheta's lattice comparison for the
actual integral-coset input; it is not a new lattice assumption. -/
theorem integralLattice_discrete (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B) :
    DiscreteTopology (integralLattice B.rationalPosition) := by
  let f := Intrinsic.OneFormsIntrinsic.cosetInput F (3 * m) 1 one_ne_zero (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition 0)
  obtain ⟨L, hL, φ, _, hsupp, _⟩ := hTheta.1 f
  let := hL
  have hle : integralLattice B.rationalPosition ≤ L := by
    rintro x ⟨r, rfl⟩
    by_contra hx
    have hz := hsupp ((integerPosition (F := F)) r) hx
    have hv := Intrinsic.OneFormsIntrinsic.cosetInput_rational_value F (3 * m) 1 one_ne_zero 0 ((integerPosition (F := F)) r)
    have hr : ∃ t : Fin (3 * m) → 𝓞 F,
        (integerPosition (F := F)) r = 0 + (1 : F) • (fun i => (t i : F)) := by
      exact ⟨r, by simp [integerPosition]⟩
    rw [ite_eq_left hr] at hv
    exact one_ne_zero (hv.symm.trans hz)
  exact (Topology.IsEmbedding.inclusion hle).discreteTopology

end RepresentationTheory.Theta.OneFormsIntrinsicLattice.Intrinsic

namespace RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicSparse

/-! Sparse inputs are actual finite Schwartz tensors. Their literal rational
theta sums agree with the Gaussian lattice sums, term by term. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Intrinsic.OneFormsIntrinsic OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

def sparseInput (a : Intrinsic.integralLattice B.rationalPosition) (n : ℕ) :
    Adelic.FiniteSchwartz.finiteSchwartz F (3 * m) :=
  Intrinsic.OneFormsIntrinsic.cosetInput F (3 * m) (n + 1 : F) (by exact_mod_cast Nat.succ_ne_zero n)
    (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (Intrinsic.latticePosition B.rationalPosition a))

theorem sparseInput_lattice_value
    (a x : Intrinsic.integralLattice B.rationalPosition) (n : ℕ) :
    Adelic.DataTheta.rationalWeight (sparseInput B a n) (Intrinsic.latticePosition B.rationalPosition x) =
      if AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset (Intrinsic.integralLattice B.rationalPosition) n a x then 1 else 0 := by
  change Adelic.Evaluation.finiteSchwartzFunction F (3 * m)
    (Intrinsic.OneFormsIntrinsic.cosetInput F (3 * m) (n + 1 : F) _
      (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (Intrinsic.latticePosition B.rationalPosition a)))
    (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (Intrinsic.latticePosition B.rationalPosition x)) = _
  rw [Intrinsic.OneFormsIntrinsic.cosetInput_rational_value]
  change (if ∃ r : Fin (3 * m) → 𝓞 F,
      Intrinsic.latticePosition B.rationalPosition x = Intrinsic.latticePosition B.rationalPosition a +
        (n + 1 : F) • (Intrinsic.integerPosition (F := F)) r then 1 else 0) = _
  rw [Intrinsic.sparse_coordinates_iff]

theorem sparseInput_support
    (a : Intrinsic.integralLattice B.rationalPosition) (n : ℕ)
    (x : Fin (3 * m) → F)
    (hx : Adelic.DataTheta.rationalWeight (sparseInput B a n) x ≠ 0) :
    x ∈ Set.range (Intrinsic.latticePosition B.rationalPosition) := by
  have hv := Intrinsic.OneFormsIntrinsic.cosetInput_rational_value F (3 * m) (n + 1 : F)
    (by exact_mod_cast Nat.succ_ne_zero n) (Intrinsic.latticePosition B.rationalPosition a) x
  change Adelic.DataTheta.rationalWeight (sparseInput B a n) x = _ at hv
  split_ifs at hv with hr
  · obtain ⟨r, rfl⟩ := hr
    apply (Intrinsic.latticePosition_range B.rationalPosition _).mpr
    rw [map_add, Intrinsic.latticePosition_coordinates]
    apply (Intrinsic.integralLattice B.rationalPosition).add_mem a.property
    have hs : (n + 1 : F) • (fun i => (r i : F)) =
        (n + 1) • (Intrinsic.integerPosition (F := F)) r := by
      ext i
      simp [Intrinsic.integerPosition, nsmul_eq_mul]
    rw [hs, map_nsmul]
    exact (Intrinsic.integralLattice B.rationalPosition).nsmul_mem
      (LinearMap.mem_range_self (Intrinsic.integerCoordinates B.rationalPosition) r) (n + 1)
  · exact False.elim (hx hv)

theorem rationalTheta_sparseInput
    (a : Intrinsic.integralLattice B.rationalPosition) (n : ℕ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    Adelic.DataTheta.rationalTheta B (sparseInput B a n) Z.matrix ξ =
      Z.phase.thetaSeriesOn (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A))
        (Intrinsic.integralLattice B.rationalPosition)
        {x | AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset (Intrinsic.integralLattice B.rationalPosition) n a x} ξ := by
  unfold Adelic.DataTheta.rationalTheta
  rw [← (Intrinsic.latticePosition_injective B.rationalPosition).tsum_eq
    (show Function.support (Adelic.DataTheta.thetaSummand B (sparseInput B a n) Z.matrix ξ) ⊆
      Set.range (Intrinsic.latticePosition B.rationalPosition) from ?_)]
  · apply tsum_congr
    intro x
    have hc := Intrinsic.latticePosition_coordinates B.rationalPosition x
    change (fun i => (B.rationalPosition (Intrinsic.latticePosition B.rationalPosition x) i : ℝ)) = x.val at hc
    simp only [Adelic.DataTheta.thetaSummand, sparseInput_lattice_value, hc,
      AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTermOn, Set.mem_ofPred_eq]
    split_ifs
    · simp [Adelic.DataTheta.gaussianValue, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase,
        AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]
    · simp
  · intro x hx
    apply sparseInput_support B a n x
    intro hzero
    exact hx (by simp [Adelic.DataTheta.thetaSummand, hzero])

theorem sparseInput_first (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (a : Intrinsic.integralLattice B.rationalPosition) (n : ℕ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) :
    fderiv ℂ (Adelic.DataTheta.completedTheta B (sparseInput B a n) Z.matrix) 0 =
      Z.phase.sparseThetaGradient (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A))
        (Intrinsic.integralLattice B.rationalPosition) a n := by
  let := Intrinsic.integralLattice_discrete B hTheta
  let S := {x | AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset (Intrinsic.integralLattice B.rationalPosition) n a x}
  have hraw := funext (rationalTheta_sparseInput B a n Z)
  have hd : HasFDerivAt (Adelic.DataTheta.rationalTheta B (sparseInput B a n) Z.matrix)
      (Z.phase.thetaSeriesOnDerivative (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A))
        (Intrinsic.integralLattice B.rationalPosition) S 0) 0 := by
    rw [hraw]
    exact Z.phase.thetaSeriesOn_hasFDerivAt _ _ S 0
  have hc := AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletion_mul_hasFDerivAt_zero
    (((Real.pi : ℂ) / 2) • AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹)) hd
  exact hc.fderiv.trans (Z.phase.fderiv_thetaSeriesOn _ _ S 0).symm

/-- Full cotangent spanning for the actual rational completed theta
construction, before its geometric frame and μ̄ projection. -/
theorem completed_first_span (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) :
    Submodule.span ℂ (Set.range (fun f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m) =>
      fderiv ℂ (Adelic.DataTheta.completedTheta B f Z.matrix) 0)) = ⊤ := by
  let := Intrinsic.integralLattice_discrete B hTheta
  apply top_unique
  rw [← Z.phase.span_sparseThetaGradients_eq_top
    (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (Adelic.BallGeometryData.FrameIndex A)) (Intrinsic.integralLattice B.rationalPosition)
    (Intrinsic.integralLattice_pairing_span B.rationalPosition)]
  apply Submodule.span_mono
  rintro v ⟨⟨a, n⟩, rfl⟩
  exact ⟨sparseInput B a n, sparseInput_first B hTheta a n Z⟩

end RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicSparse

namespace RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

/-! The actual multiplicity-one μ̄ projection, with an explicit right inverse. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicSparse

abbrev Cotangent := (Fin 2 → ℂ) →L[ℂ] ℂ

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K}

def slot (i : Fin 2) : Adelic.BallGeometryData.FrameIndex A := (A.distinguished, i.succ, 0)

def slotEmbedding : (Fin 2 → ℂ) →L[ℂ] (Adelic.BallGeometryData.FrameIndex A → ℂ) :=
  (ContinuousLinearMap.proj 0).smulRight (Pi.single (slot (A := A) 0) 1) +
    (ContinuousLinearMap.proj 1).smulRight (Pi.single (slot (A := A) 1) 1)

def slotSelection : (Adelic.BallGeometryData.FrameIndex A → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (slot (A := A) i)

theorem slotSelection_embedding (u : Fin 2 → ℂ) :
    slotSelection (A := A) (slotEmbedding (A := A) u) = u := by
  funext i
  fin_cases i <;> simp [slotSelection, slotEmbedding, slot]

variable (B : Adelic.DataTheta.ComparisonData F H K A)

def cotangentProjection (z : Adelic.BallNatural.Ball) :
    ((Adelic.BallGeometryData.FrameIndex A → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] Cotangent where
  toFun l := (B.halfFrame z)⁻¹ •
    (l.comp (Matrix.toLin' (B.frame z).invᵀ).toContinuousLinearMap).comp slotEmbedding
  map_add' l r := by ext u; simp
  map_smul' c l := by ext u; simp [mul_left_comm]

def thetaOneForm (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : Adelic.BallNatural.Ball) : Cotangent :=
  cotangentProjection B z (fderiv ℂ (Adelic.DataTheta.completedTheta B f (B.period z).matrix) 0)

def geometricFirst (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : Adelic.BallNatural.Ball) :
    (Adelic.BallGeometryData.FrameIndex A → ℂ) →L[ℂ] ℂ :=
  (B.halfFrame z)⁻¹ • (fderiv ℂ (Adelic.DataTheta.completedTheta B f (B.period z).matrix) 0).comp
    (Matrix.toLin' (B.frame z).invᵀ).toContinuousLinearMap

theorem geometricTensor_one_apply (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : Adelic.BallNatural.Ball)
    (v : Fin 1 → Adelic.BallGeometryData.FrameIndex A → ℂ) :
    Adelic.DataTheta.geometricTensor B f 1 z v = geometricFirst B f z (v 0) := by
  simp [Adelic.DataTheta.geometricTensor, geometricFirst, Adelic.DataTheta.completedTensor, iteratedFDeriv_one_apply]

theorem thetaOneForm_apply (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : Adelic.BallNatural.Ball) (u : Fin 2 → ℂ) :
    thetaOneForm B f z u = geometricFirst B f z (slotEmbedding u) := rfl

/-- This is literally the order-one geometric tensor evaluated in the
two distinguished annihilator slots. -/
theorem thetaOneForm_geometricTensor
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : Adelic.BallNatural.Ball) (u : Fin 2 → ℂ) :
    thetaOneForm B f z u =
      Adelic.DataTheta.geometricTensor B f 1 z (fun _ => slotEmbedding (A := A) u) := by
  simp [thetaOneForm, cotangentProjection, Adelic.DataTheta.geometricTensor, Adelic.DataTheta.completedTensor,
    iteratedFDeriv_one_apply]

theorem cotangentProjection_surjective (hGeometry : Adelic.DataTheta.GeometryIdentification B)
    (z : Adelic.BallNatural.Ball) : Function.Surjective (cotangentProjection B z) := by
  obtain ⟨_, _, _, _, _, hhalf, _⟩ := hGeometry
  have hh := (hhalf z).1
  intro η
  let l : (Adelic.BallGeometryData.FrameIndex A → ℂ) →L[ℂ] ℂ :=
    B.halfFrame z • (η.comp slotSelection).comp
      (Matrix.toLin' (B.frame z).valᵀ).toContinuousLinearMap
  refine ⟨l, ?_⟩
  ext u
  change (B.halfFrame z)⁻¹ * (B.halfFrame z *
    η (slotSelection ((B.frame z).valᵀ.mulVec
      ((B.frame z).invᵀ.mulVec (slotEmbedding u))))) = η u
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, (B.frame z).inv_val,
    Matrix.transpose_one, Matrix.one_mulVec, slotSelection_embedding]
  rw [← mul_assoc, inv_mul_cancel₀ hh, one_mul]

/-- The geometric μ̄ one-forms span the actual affine-ball cotangent. -/
theorem thetaOneForm_span
    (hGeometry : Adelic.DataTheta.GeometryIdentification B) (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (z : Adelic.BallNatural.Ball) :
    Submodule.span ℂ (Set.range (fun f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1) =>
      thetaOneForm B f z)) = ⊤ := by
  change Submodule.span ℂ (Set.range (fun f => cotangentProjection B z
    (fderiv ℂ (Adelic.DataTheta.completedTheta B f (B.period z).matrix) 0))) = ⊤
  rw [Set.range_comp' (cotangentProjection B z), Submodule.span_image,
    IntrinsicSparse.completed_first_span B hTheta, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (cotangentProjection_surjective B hGeometry z)

end RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

namespace RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCotangentAction

/-! Identify the natural line times annihilator action with the differential
of the actual projective ball action. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

theorem denominator_differentiable (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Differentiable ℂ (Adelic.DeterminantCoordinates.denominator g) := by
  unfold Adelic.DeterminantCoordinates.denominator Adelic.DeterminantCoordinates.lineVector Matrix.mulVec dotProduct
  simp [Fin.sum_univ_succ]
  fun_prop

theorem chartImage_differentiableAt (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (z : Fin 2 → ℂ) (hz : Adelic.DeterminantCoordinates.denominator g z ≠ 0) :
    DifferentiableAt ℂ (Adelic.DeterminantCoordinates.chartImage g) z := by
  apply differentiableAt_pi.mpr
  intro i
  change DifferentiableAt ℂ
    (fun y => g.val.mulVec (Adelic.DeterminantCoordinates.lineVector y) i.castSucc / Adelic.DeterminantCoordinates.denominator g y) z
  simp only [div_eq_mul_inv]
  apply DifferentiableAt.mul _ ((denominator_differentiable g z).inv hz)
  unfold Adelic.DeterminantCoordinates.lineVector Matrix.mulVec dotProduct
  simp [Fin.sum_univ_succ]
  fun_prop

def columnCovector (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (z : Fin 2 → ℂ) (j : Fin 2) : IntrinsicProjection.Cotangent :=
  ∑ i : Fin 2, Adelic.DeterminantCoordinates.dualCoordinates g z i j • ContinuousLinearMap.proj i

theorem projective_pairing (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (z y : Fin 2 → ℂ) (hy : Adelic.DeterminantCoordinates.denominator g y ≠ 0) (j : Fin 2) :
    Adelic.DeterminantCoordinates.denominator g y * (columnCovector g z j (Adelic.DeterminantCoordinates.chartImage g y) + Adelic.DeterminantCoordinates.dualColumn g z j 2) =
      y j - z j := by
  have h := Adelic.AnnihilatorFrame.inverseTranspose_pairing g (Adelic.DeterminantCoordinates.lineVector y) (Adelic.DeterminantCoordinates.annihilatorVector z j)
  rw [Adelic.DeterminantCoordinates.lineVector_chartImage g y hy, smul_dotProduct] at h
  fin_cases j <;>
    simpa [columnCovector, Adelic.DeterminantCoordinates.dualCoordinates, Adelic.DeterminantCoordinates.dualColumn, Adelic.DeterminantCoordinates.lineVector,
      Adelic.DeterminantCoordinates.annihilatorVector, dotProduct, Fin.sum_univ_succ, mul_comm, mul_left_comm,
      mul_assoc, sub_eq_add_neg, add_assoc] using h

theorem cotangent_column_derivative (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (z : Fin 2 → ℂ) (hz : Adelic.DeterminantCoordinates.denominator g z ≠ 0) (j : Fin 2) :
    Adelic.DeterminantCoordinates.denominator g z • (columnCovector g z j).comp (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage g) z) =
      ContinuousLinearMap.proj j := by
  let l := columnCovector g z j
  let c := Adelic.DeterminantCoordinates.dualColumn g z j 2
  have hzero : l (Adelic.DeterminantCoordinates.chartImage g z) + c = 0 := by
    have h := projective_pairing g z z hz j
    rw [sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left hz
  have hd := (denominator_differentiable g z).hasFDerivAt.mul
    ((l.hasFDerivAt.comp z (chartImage_differentiableAt g z hz).hasFDerivAt).add_const c)
  have hd' : HasFDerivAt
      (fun y => Adelic.DeterminantCoordinates.denominator g y * (l (Adelic.DeterminantCoordinates.chartImage g y) + c))
      (Adelic.DeterminantCoordinates.denominator g z • l.comp (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage g) z)) z := by
    change HasFDerivAt (fun y => Adelic.DeterminantCoordinates.denominator g y * (l (Adelic.DeterminantCoordinates.chartImage g y) + c))
      (Adelic.DeterminantCoordinates.denominator g z • l.comp (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage g) z) +
        (l (Adelic.DeterminantCoordinates.chartImage g z) + c) • fderiv ℂ (Adelic.DeterminantCoordinates.denominator g) z) z at hd
    have hzD : (0 : ℂ) • fderiv ℂ (Adelic.DeterminantCoordinates.denominator g) z = 0 := by
      ext u
      exact zero_mul _
    rw [hzero, hzD, add_zero] at hd
    exact hd
  have he : (fun y : Fin 2 → ℂ => y j - z j) =ᶠ[nhds z]
      (fun y => Adelic.DeterminantCoordinates.denominator g y * (l (Adelic.DeterminantCoordinates.chartImage g y) + c)) := by
    filter_upwards [((denominator_differentiable g).continuous.isOpen_preimage
      _ isOpen_ne).mem_nhds hz] with y hy
    exact (projective_pairing g z y hy j).symm
  exact (hd'.congr_of_eventuallyEq he).unique
    ((ContinuousLinearMap.proj j : IntrinsicProjection.Cotangent).hasFDerivAt.sub_const (z j))

theorem cotangent_derivative (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (z u : Fin 2 → ℂ) (hz : Adelic.DeterminantCoordinates.denominator g z ≠ 0) :
    Adelic.DeterminantCoordinates.denominator g z • (Adelic.DeterminantCoordinates.dualCoordinates g z).transpose.mulVec
      (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage g) z u) = u := by
  funext j
  have h := congrArg (fun l : IntrinsicProjection.Cotangent => l u) (cotangent_column_derivative g z hz j)
  fin_cases j <;>
    simpa [columnCovector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_add] using h

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

theorem frame_slot_row (hGeometry : Adelic.DataTheta.GeometryIdentification B)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball)
    (i : Fin 2) (q : Adelic.BallGeometryData.FrameIndex A) :
    Adelic.BallGeometryData.frameMatrix A g z (IntrinsicProjection.slot (A := A) i) q =
      if q = IntrinsicProjection.slot (A := A) 0 then Adelic.DeterminantCoordinates.dualCoordinates (Adelic.BallNatural.asSL (B.ball g)) z.val i 0
      else if q = IntrinsicProjection.slot (A := A) 1 then Adelic.DeterminantCoordinates.dualCoordinates (Adelic.BallNatural.asSL (B.ball g)) z.val i 1
      else 0 := by
  have hinv : (Adelic.BallGeometryData.standardMatrix A g A.distinguished)⁻¹ = ((Adelic.BallNatural.asSL (B.ball g))⁻¹).val := by
    rw [← hGeometry.2.1 g, Matrix.inv_def, (Adelic.BallNatural.asSL (B.ball g)).property]
    simp [Matrix.SpecialLinearGroup.coe_inv]
  rcases q with ⟨v, j, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    by_cases hv : v = A.distinguished
  all_goals
    simp [Adelic.BallGeometryData.frameMatrix, Adelic.BallGeometryData.geometricCoordinates, Adelic.BallGeometryData.geometricAction, Adelic.BallGeometryData.geometricFrame,
      IntrinsicProjection.slot, hinv, Adelic.DeterminantCoordinates.dualCoordinates, Adelic.DeterminantCoordinates.dualColumn, Adelic.DeterminantCoordinates.annihilatorVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, hv, Ne.symm, Pi.single_apply]

end RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCotangentAction

namespace RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCovariance

/-! Rational covariance of the actual ordinary holomorphic theta one-forms. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCotangentAction

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

theorem frame_transpose_embedding (hGeometry : Adelic.DataTheta.GeometryIdentification B)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (u : Fin 2 → ℂ) :
    (Adelic.BallGeometryData.frameMatrix A g z).transpose.mulVec (IntrinsicProjection.slotEmbedding (A := A) u) =
      IntrinsicProjection.slotEmbedding (A := A)
        ((Adelic.DeterminantCoordinates.dualCoordinates (Adelic.BallNatural.asSL (B.ball g)) z.val).transpose.mulVec u) := by
  funext q
  change ((Adelic.BallGeometryData.frameMatrix A g z).transpose.mulVec
    (u 0 • Pi.single (IntrinsicProjection.slot (A := A) 0) 1 + u 1 • Pi.single (IntrinsicProjection.slot (A := A) 1) 1)) q = _
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.mulVec_single, MulOpposite.op_one,
    one_smul, Matrix.col, Matrix.transpose_apply, smul_eq_mul]
  rw [IntrinsicCotangentAction.frame_slot_row B hGeometry g z 0 q, IntrinsicCotangentAction.frame_slot_row B hGeometry g z 1 q]
  by_cases hq0 : q = IntrinsicProjection.slot (A := A) 0
  · subst q
    simp [IntrinsicProjection.slotEmbedding, IntrinsicProjection.slot, mul_comm]
  · by_cases hq1 : q = IntrinsicProjection.slot (A := A) 1
    · subst q
      simp [IntrinsicProjection.slotEmbedding, IntrinsicProjection.slot, mul_comm]
    · simp [IntrinsicProjection.slotEmbedding, hq0, hq1]

theorem thetaOneForm_covariance
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hd C P)
    (hGeometry : Adelic.DataTheta.GeometryIdentification B) (hCovariance : Adelic.DataTheta.Descent.RationalHeckeCovariance B P hd C D)
    (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : Adelic.BallNatural.Ball) (u : Fin 2 → ℂ) :
    IntrinsicProjection.thetaOneForm B (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f)
        (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)
        (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val u) =
      IntrinsicProjection.thetaOneForm B f z u := by
  let gA := Adelic.RationalSU.rationalArchimedeanSU F H g
  let gB := B.ball gA
  let M := Adelic.BallGeometryData.frameMatrix A gA z
  let u' := fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val u
  have hEmbed := frame_transpose_embedding B hGeometry gA z u'
  obtain ⟨_, _, _, _, _, _, _, _, _, hdet, _⟩ := hGeometry
  have hunit : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    change (Adelic.BallGeometryData.frameMatrix A gA z).det ≠ 0
    rw [hdet, pow_one, Adelic.DeterminantCoordinates.hodgeDeterminantFactor_eq]
    exact pow_ne_zero 2 (Adelic.BallNatural.denominator_ne_zero gB z)
  have hcancel : Adelic.BallGeometryData.dualFrameChange A gA z (M.transpose.mulVec (IntrinsicProjection.slotEmbedding u')) =
      IntrinsicProjection.slotEmbedding (A := A) u' := by
    unfold Adelic.BallGeometryData.dualFrameChange
    change M⁻¹ᵀ.mulVec (Mᵀ.mulVec (IntrinsicProjection.slotEmbedding u')) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv M hunit, Matrix.transpose_one, Matrix.one_mulVec]
  have hc := (hCovariance g f).2.2.2 1 z
    (fun _ => M.transpose.mulVec (IntrinsicProjection.slotEmbedding (A := A) u'))
  simp only [IntrinsicProjection.geometricTensor_one_apply] at hc
  change IntrinsicProjection.geometricFirst B _ _ (Adelic.BallGeometryData.dualFrameChange A gA z
      (M.transpose.mulVec (IntrinsicProjection.slotEmbedding u'))) =
    Adelic.BallNatural.Factors.naturalHalfFactor 1 gB z * IntrinsicProjection.geometricFirst B f z
      (M.transpose.mulVec (IntrinsicProjection.slotEmbedding u')) at hc
  rw [hcancel] at hc
  have harg : Adelic.DeterminantCoordinates.denominator (Adelic.BallNatural.asSL gB) z.val •
      M.transpose.mulVec (IntrinsicProjection.slotEmbedding (A := A) u') = IntrinsicProjection.slotEmbedding (A := A) u := by
    rw [hEmbed]
    rw [← map_smul, IntrinsicCotangentAction.cotangent_derivative _ _ _ (Adelic.BallNatural.denominator_ne_zero gB z)]
  change IntrinsicProjection.geometricFirst B _ _ (IntrinsicProjection.slotEmbedding u') = IntrinsicProjection.geometricFirst B f z (IntrinsicProjection.slotEmbedding u)
  rw [hc]
  rw [Adelic.BallNatural.Factors.naturalHalfFactor, pow_one, Adelic.BallNatural.Factors.automorphyFactor]
  change Adelic.DeterminantCoordinates.denominator (Adelic.BallNatural.asSL gB) z.val • IntrinsicProjection.geometricFirst B f z
    (M.transpose.mulVec (IntrinsicProjection.slotEmbedding u')) = _
  rw [← map_smul, harg]

end RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCovariance

namespace RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicDescent

/-! Genuine principal congruence levels for the native theta one-forms. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCovariance

theorem finite_spanning_family {Φ V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Φ → V)
    (hspan : Submodule.span ℂ (Set.range f) = ⊤) :
    ∃ s : Finset Φ, Submodule.span ℂ (f '' (s : Set Φ)) = ⊤ := by
  obtain ⟨b, hb, hbspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range f)
  choose φ hφ using hb
  refine ⟨Finset.univ.image φ, ?_⟩
  apply top_unique
  rw [← hbspan.trans hspan]
  apply Submodule.span_mono
  rintro v ⟨j, rfl⟩
  exact ⟨φ j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hφ j⟩

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hd C P)

/-- Ordinary one-form invariance at an actual torsion-free principal
level, refining an arbitrary initial open subgroup and integer level. -/
theorem thetaOneForm_principal_descent
    (hGeometry : Adelic.DataTheta.GeometryIdentification B) (hCovariance : Adelic.DataTheta.Descent.RationalHeckeCovariance B P hd C D)
    (hDescent : Adelic.DataTheta.Descent.CongruenceDescent B P hd C D)
    (Φ : Finset (Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1))) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H))
    (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
        (∀ f ∈ Φ, ∀ g ∈ L, Adelic.FiniteSchwartz.finiteAction F H K hd C P D g f = f) ∧
        ∀ f ∈ Φ, ∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ z : Adelic.BallNatural.Ball, ∀ u : Fin 2 → ℂ,
          IntrinsicProjection.thetaOneForm B f (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)
              (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val u) =
            IntrinsicProjection.thetaOneForm B f z u := by
  obtain ⟨N, hN, hdiv, htorsion, L, hLc, hL₀, hcontains, hfix, _⟩ :=
    hDescent Φ K₀ N₀ hN₀
  refine ⟨N, hN, hdiv, htorsion, L, hLc, hL₀, hcontains, hfix, ?_⟩
  intro f hf g hg z u
  have h := IntrinsicCovariance.thetaOneForm_covariance B P hd C D hGeometry hCovariance g f z u
  rw [hfix f hf _ (hcontains g hg)] at h
  exact h

/-- At each point, a spanning family is fixed at one genuine principal
level refining any prescribed initial level. -/
theorem thetaOneForm_principal_spanning
    (hGeometry : Adelic.DataTheta.GeometryIdentification B) (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (hDescent : Adelic.DataTheta.Descent.CongruenceDescent B P hd C D)
    (z : Adelic.BallNatural.Ball) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H)) (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
        Submodule.span ℂ {ω : IntrinsicProjection.Cotangent | ∃ f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1),
          (∀ g ∈ L, Adelic.FiniteSchwartz.finiteAction F H K hd C P D g f = f) ∧ ω = IntrinsicProjection.thetaOneForm B f z} = ⊤ := by
  obtain ⟨Φ, hspan⟩ := finite_spanning_family (fun f => IntrinsicProjection.thetaOneForm B f z)
    (IntrinsicProjection.thetaOneForm_span B hGeometry hTheta z)
  obtain ⟨N, hN, hdiv, htorsion, L, hLc, hL₀, hcontains, hfix, _⟩ :=
    hDescent Φ K₀ N₀ hN₀
  refine ⟨N, hN, hdiv, htorsion, L, hLc, hL₀, hcontains, ?_⟩
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro ω ⟨f, hf, rfl⟩
  exact ⟨f, hfix f hf, rfl⟩

end RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicDescent

end

end OAI
