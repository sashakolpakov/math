import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TransportNew
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceFamily
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicRefinement
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateComparison

/-! # Period Total -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodTotal.CM

noncomputable section

section

/-! Assemble the concrete principal surfaces and four period lines.
All fields are constructed from the arithmetic hypotheses and full ReferenceFamily;
theta descent, extraction and nonvanishing are not fields of this setup. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open _root_.Module

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

structure RationalPeriodApproximation
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (P : Lagrangians.CM.LagrangianPair K B places (fun i τ => FourSplittings.CM.initialThetaSigns K v i (places.representative τ)))
    (ε : ℝ) where
  basis : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)
  orthogonal : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (basis 0) (basis 1) = 0
  nondegenerate : ∀ i, Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (basis i) (basis i) ≠ 0
  orthocomplement : ∀ y, y ∈ Submodule.span K {basis 1} ↔
    Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (basis 0) y = 0
  coefficient_signs : ∀ i τ, 0 <
    (ComplexMultiplication.SignSwitch.CM.signValue (FourSplittings.CM.newThetaSigns K v i (places.representative τ)) : ℝ) *
      (-(HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).im) *
        (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (basis i) (basis i))).re
  periods : (i : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (FourSplittings.CM.newThetaSigns K v i)
  coefficients : ∀ i,
    (periods i).coordinates.a = Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (basis i) (basis i) ∧
      (periods i).coordinates.delta = P.delta
  compact_close : ∀ τ, dist
    (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) basis
      (fun i => FourSplittings.CM.newThetaSigns K v i (places.representative τ)))
    (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) (Pi.basisFun K (Fin 2))
      (fun i => FourSplittings.CM.initialThetaSigns K v i (places.representative τ))) < ε

structure FourPeriodSetup
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)) (Nbase : ℕ) where
  ball : HeckeCycles.GeometricSource.CM.BallDatum K
  places : HeckeCycles.GeometricSource.CM.Places K
  depth : ℕ
  depth_ge_three : 3 ≤ depth
  base_divides : Nbase ∣ depth
  surface : (N : ℕ) → 0 < N → depth ∣ N → Cm.PrincipalBallSurface K ball N
  pair : Lagrangians.CM.LagrangianPair K ball places (fun i τ => FourSplittings.CM.initialThetaSigns K v i (places.representative τ))
  initialPeriods : (i : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K ball places (FourSplittings.CM.initialThetaSigns K v i)
  initial_coefficients : ∀ i,
    (initialPeriods i).coordinates.a = pair.a i ∧ (initialPeriods i).coordinates.delta = pair.delta
  approximate : ∀ ε : ℝ, 0 < ε → Nonempty (RationalPeriodApproximation K v ball places pair ε)

theorem exists_four_period_setup (hReferenceFamily : Moduli.CM.ReferenceFamilyInput)
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (hb : ∀ τ, ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
      ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (hi : ∀ i, (v i).val 1 = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
    (Nbase : ℕ) (hNbase : 0 < Nbase) : Nonempty (FourPeriodSetup K v Nbase) := by
  obtain ⟨B₀⟩ := BallDatum.CM.exists_ball_datum K hother
  let places := Places.CM.placesFromType K (v 0) (hi 0)
  obtain ⟨B, _, N₀, hN₀, hbase, hsurf⟩ :=
    SurfaceFamily.CM.exists_principal_surface_family K hReferenceFamily B₀ places (fun _ => false) Nbase hNbase
  obtain ⟨P, L, hL, happ⟩ := FourSplittings.CM.exists_four_pattern_splittings K B places v hb hi
  refine ⟨{
    ball := B
    places := places
    depth := N₀
    depth_ge_three := hN₀
    base_divides := hbase
    surface := fun N hn hd => Classical.choice (hsurf N hn hd)
    pair := P
    initialPeriods := L
    initial_coefficients := hL
    approximate := ?_
  }⟩
  intro ε hε
  obtain ⟨b, horth, hnd, hcompl, hsign, hdist⟩ := happ ε hε
  have hμ : ∀ i, FourSplittings.CM.newThetaSigns K v i 1 = true := by
    intro i
    fin_cases i <;> simp [FourSplittings.CM.newThetaSigns, FourSplittings.CM.thetaSign, hi]
  obtain ⟨Ln, hLn⟩ := TransportNew.CM.new_line_periods_on_original_space K (FourSplittings.CM.initialThetaSigns K v)
    (FourSplittings.CM.newThetaSigns K v) P hμ b hnd hsign
  exact ⟨⟨b, horth, hnd, hcompl, hsign, Ln, hLn, hdist⟩⟩

theorem setup_principal_refinement
    {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
    (D : FourPeriodSetup K v Nbase) (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hDN : D.depth ∣ N) (hDM : D.depth ∣ M) (hNM : N ∣ M) :
    Nonempty (Cm.PrincipalRefinement K (D.surface N hN hDN) (D.surface M hM hDM)) :=
  IntrinsicRefinement.CM.principal_refinement_of_dvd D.ball N M _ _ hNM

end

section

/-! ThetaCycle: rational symplectic coordinates on the same total tensor space. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def tensorLineCoordinates : TransportNew.CM.TensorPositions K ≃ₗ[ℚ] (Fin 2 → HeckeCycles.GeometricSource.CM.Vec K) where
  toFun x i j := x j i
  invFun x j i := x i j
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev TotalPositions (places : HeckeCycles.GeometricSource.CM.Places K) := Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places)

/-- The two line coordinate systems are assembled into one position block
and one momentum block, in the index order of the fixed total theta input. -/
def totalSymplecticCoordinates (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) :
    TransportNew.CM.TensorPositions K ≃ₗ[ℚ] (Sum (TotalPositions K places) (TotalPositions K places) → ℚ) :=
  (tensorLineCoordinates K).trans <|
    (LinearEquiv.finTwoArrow ℚ (HeckeCycles.GeometricSource.CM.Vec K)).trans <|
    ((C 0).rational.prodCongr (C 1).rational).trans <|
    (LinearEquiv.prodProdProdComm ℚ _ _ _ _).trans <|
    ((LinearEquiv.sumArrowLequivProdArrow (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℚ ℚ).symm.prodCongr
      (LinearEquiv.sumArrowLequivProdArrow (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℚ ℚ).symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (TotalPositions K places) (TotalPositions K places) ℚ ℚ).symm

theorem total_symplectic_coordinates_pairing
    (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (δ : K) (a : Fin 2 → K)
    (hc : ∀ i, (C i).a = a i ∧ (C i).delta = δ) (x y : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (totalSymplecticCoordinates K C x) (totalSymplecticCoordinates K C y) =
      Algebra.trace ℚ K (δ * TransportNew.CM.tensorHermitian K B.b a x y) := by
  change (∑ j : TotalPositions K places, _) = _
  rw [Fintype.sum_sum_type]
  change (∑ j, (((C 0).rational (fun k => x k 0)).1 j *
      ((C 0).rational (fun k => y k 0)).2 j -
      ((C 0).rational (fun k => x k 0)).2 j * ((C 0).rational (fun k => y k 0)).1 j)) +
    (∑ j, (((C 1).rational (fun k => x k 1)).1 j *
      ((C 1).rational (fun k => y k 1)).2 j -
      ((C 1).rational (fun k => x k 1)).2 j * ((C 1).rational (fun k => y k 1)).1 j)) = _
  have hs (i : Fin 2) :
      (∑ j, (((C i).rational (fun k => x k i)).1 j *
        ((C i).rational (fun k => y k i)).2 j -
        ((C i).rational (fun k => x k i)).2 j * ((C i).rational (fun k => y k i)).1 j)) =
      Algebra.trace ℚ K ((C i).delta * (C i).a *
        HeckeCycles.GeometricSource.CM.hermitian K B.b (fun k => x k i) (fun k => y k i)) := by
    rw [(C i).symplectic]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs 0, hs 1,
    (hc 0).1, (hc 0).2, (hc 1).1, (hc 1).2, TransportNew.CM.tensor_hermitian_blocks]
  simp only [Fin.sum_univ_two, mul_add, ← mul_assoc, map_add]

end

/-! ThetaCycle: the approximating basis gives an actual rational symplectic matrix. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM _root_.Module

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

/-- A vector expressed in the new line coordinates is sent to its original
coordinates in the same rational tensor space. -/
def totalBasisTransition (C D : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) :
    (Sum (TotalPositions K places) (TotalPositions K places) → ℚ) ≃ₗ[ℚ]
      (Sum (TotalPositions K places) (TotalPositions K places) → ℚ) :=
  (totalSymplecticCoordinates K D).symm.trans <|
    ((TransportNew.CM.tensorBasisChange K b).restrictScalars ℚ).trans (totalSymplecticCoordinates K C)

theorem total_basis_transition_pairing
    (C D : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (δ : K) (a : Fin 2 → K)
    (ha : ∀ i, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (horth : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0)
    (hc : ∀ i, (C i).a = a i ∧ (C i).delta = δ)
    (hd : ∀ i, (D i).a = Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i) ∧ (D i).delta = δ)
    (x y : Sum (TotalPositions K places) (TotalPositions K places) → ℚ) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (totalBasisTransition K C D b x) (totalBasisTransition K C D b y) =
      RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing x y := by
  change RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing
    (totalSymplecticCoordinates K C (TransportNew.CM.tensorBasisChange K b ((totalSymplecticCoordinates K D).symm x)))
    (totalSymplecticCoordinates K C (TransportNew.CM.tensorBasisChange K b ((totalSymplecticCoordinates K D).symm y))) = _
  rw [total_symplectic_coordinates_pairing K C δ a hc,
    TransportNew.CM.tensor_trace_basis_isometry K B.b δ a ha b horth,
    ← total_symplectic_coordinates_pairing K D δ _ hd]
  simp only [LinearEquiv.apply_symm_apply]

def totalBasisMatrix (C D : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) :=
  LinearMap.toMatrix' (totalBasisTransition K C D b).toLinearMap

theorem total_basis_matrix_coordinates
    (C D : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) (x : TransportNew.CM.TensorPositions K) :
    totalBasisMatrix K C D b *ᵥ (totalSymplecticCoordinates K D x) =
      totalSymplecticCoordinates K C (TransportNew.CM.tensorBasisChange K b x) := by
  change Matrix.toLin' (LinearMap.toMatrix' (totalBasisTransition K C D b).toLinearMap)
    (totalSymplecticCoordinates K D x) = _
  rw [Matrix.toLin'_toMatrix']
  change totalSymplecticCoordinates K C
    (TransportNew.CM.tensorBasisChange K b ((totalSymplecticCoordinates K D).symm (totalSymplecticCoordinates K D x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The same coordinate equation holds under every scalar extension,
including the real, complex, and finite-adelic realizations. -/
theorem total_basis_matrix_baseChange {R : Type*} [CommRing R] (f : ℚ →+* R)
    (C D : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) (x : TransportNew.CM.TensorPositions K) :
    (totalBasisMatrix K C D b).map f *ᵥ (fun i => f (totalSymplecticCoordinates K D x i)) =
      fun i => f (totalSymplecticCoordinates K C (TransportNew.CM.tensorBasisChange K b x) i) := by
  funext i
  have hm := f.map_mulVec (totalBasisMatrix K C D b) (totalSymplecticCoordinates K D x) i
  rw [total_basis_matrix_coordinates] at hm
  exact hm.symm

theorem total_basis_matrix_symplectic
    (C D : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (δ : K) (a : Fin 2 → K)
    (ha : ∀ i, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (horth : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0)
    (hc : ∀ i, (C i).a = a i ∧ (C i).delta = δ)
    (hd : ∀ i, (D i).a = Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i) ∧ (D i).delta = δ) :
    totalBasisMatrix K C D b ∈ Matrix.symplecticGroup (TotalPositions K places) ℚ := by
  apply RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.preserving_coordinatePairing_symplectic
  intro x y
  change RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing
    ((LinearMap.toMatrix' (totalBasisTransition K C D b).toLinearMap) *ᵥ x)
    ((LinearMap.toMatrix' (totalBasisTransition K C D b).toLinearMap) *ᵥ y) = _
  simp only [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', LinearEquiv.coe_coe]
  exact total_basis_transition_pairing K C D δ a ha b horth hc hd x y

/-- The change of splitting is an element of the literal rational symplectic
group used by the total finite Weil action. All its data come from the setup. -/
def approximationSymplecticMatrix [IsGalois ℚ K]
    {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
    (D : FourPeriodSetup K v Nbase) {ε : ℝ}
    (A : RationalPeriodApproximation K v D.ball D.places D.pair ε) :
    Matrix.symplecticGroup (TotalPositions K D.places) ℚ :=
  ⟨totalBasisMatrix K (fun i => (D.initialPeriods i).coordinates)
    (fun i => (A.periods i).coordinates) A.basis,
   total_basis_matrix_symplectic K _ _ D.pair.delta D.pair.a
    (fun i => (D.pair.a_sign i).2.1) A.basis A.orthogonal
    D.initial_coefficients A.coefficients⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodTotal.CM
