import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction
import OAI.RepresentationTheory.Theta.Geometric.Period.Ne

/-! # Unitary Eq -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames

/-! The literal CM coordinate action preserves the source's paired
forms and carries its distinguished negative line to the actual rational
period action. These are the geometric identities behind theta covariance. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E}

def localAction (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (τ : Gal(E/ℚ)) : Module.End ℂ (GeometricSource.CM.Vec ℂ) :=
  Matrix.toLin' ((g.val : Matrix (Fin 3) (Fin 3) E).map
    (E.val.toRingHom.comp τ.toRingHom))

theorem ambientOperator_apply (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (w : GeometricSource.CM.Ambient E)
    (τ : Gal(E/ℚ)) : ComplexAction.CM.ambientOperator E g w τ = localAction E g τ (w τ) := rfl

theorem conjugate_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (τ : Gal(E/ℚ)) (x : GeometricSource.CM.Vec ℂ) :
    localAction E g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) x = star (localAction E g τ (star x)) := by
  funext i
  simp [localAction, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    AlgEquiv.mul_apply, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_coe]

theorem pairing_eq_form (τ : Gal(E/ℚ)) (x y : GeometricSource.CM.Vec ℂ) :
    GeometricSource.CM.localPairing E B.b τ x y =
      Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd ℂ) ((τ B.b : E) : ℂ) x (star y) := by
  simp [GeometricSource.CM.localPairing, Geometry.ComplexBall.ArithmeticQuotientEquationsData.form, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient]

theorem pairing_preserved (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (τ : Gal(E/ℚ)) (x y : GeometricSource.CM.Vec ℂ) :
    GeometricSource.CM.localPairing E B.b τ (localAction E g τ x)
        (localAction E g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) y) = GeometricSource.CM.localPairing E B.b τ x y := by
  rw [pairing_eq_form, pairing_eq_form, conjugate_action, star_star]
  exact (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap B.b (E.val.toRingHom.comp τ.toRingHom) g).property x (star y)

def period (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : GeometricSource.CM.BallChart → GeometricSource.CM.BallChart :=
  RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm B.b E.val.toRingHom g

theorem line_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    ∃ c : ℂ, c ≠ 0 ∧ localAction E g 1 (GeometricSource.CM.BallDatum.lineVector z) =
      c • GeometricSource.CM.BallDatum.lineVector (Frames.period E g z) := by
  have hc := RepresentationTheory.Theta.Geometric.Period.Ne.periodRow_last_ne_zero B.b E.val.toRingHom g ⟨z, hz⟩
  refine ⟨RepresentationTheory.Theta.Geometric.Period.Ne.periodRow B.b E.val.toRingHom g 2 z, hc, ?_⟩
  have ha (i : Fin 3) : localAction E g 1 (GeometricSource.CM.BallDatum.lineVector z) i =
      RepresentationTheory.Theta.Geometric.Period.Ne.periodRow B.b E.val.toRingHom g i z :=
    (RepresentationTheory.Theta.Geometric.Period.Ne.periodRow_eq_mulVec B.b E.val.toRingHom g i z).symm
  funext i
  rw [ha]
  change _ = RepresentationTheory.Theta.Geometric.Period.Ne.periodRow B.b E.val.toRingHom g 2 z *
    GeometricSource.CM.BallDatum.lineVector (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm B.b E.val.toRingHom g z) i
  rw [RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_eq_fractional B.b E.val.toRingHom g z hz]
  fin_cases i
  · exact (mul_div_cancel₀ _ hc).symm
  · exact (mul_div_cancel₀ _ hc).symm
  · exact (mul_one _).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PrescribedAction

/-! The source's prescribed Lagrangian is equivariant under the actual
rational unitary action, including its distinguished line, annihilator,
and all compact-place summands. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E}

theorem localAction_one (τ : Gal(E/ℚ)) :
    Frames.localAction E (1 : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) τ = 1 := by
  simp [Frames.localAction]
  rfl

theorem localAction_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (τ : Gal(E/ℚ)) :
    Frames.localAction E (g * h) τ = Frames.localAction E g τ * Frames.localAction E h τ := by
  change Matrix.toLin' (((g.val : Matrix (Fin 3) (Fin 3) E) * h.val).map
      (E.val.toRingHom.comp τ.toRingHom)) = _
  rw [Matrix.map_mul, Matrix.toLin'_mul]
  rfl

theorem ambient_inverse (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (w : GeometricSource.CM.Ambient E) :
    ComplexAction.CM.ambientOperator E g⁻¹ (ComplexAction.CM.ambientOperator E g w) = w := by
  funext τ
  change Frames.localAction E g⁻¹ τ (Frames.localAction E g τ (w τ)) = w τ
  rw [← Module.End.mul_apply, ← localAction_mul, inv_mul_cancel, localAction_one,
    Module.End.one_apply]

theorem period_inverse (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) :
    Frames.period E g⁻¹ (Frames.period E g z) = z := by
  change RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm B.b E.val.toRingHom g⁻¹
    (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm B.b E.val.toRingHom g z) = z
  rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem period_preserves (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart)
    (hz : z ∈ B.domain) : Frames.period E g z ∈ B.domain :=
  RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_preserves B.b E.val.toRingHom g z hz

theorem pairing_smul_left (τ : Gal(E/ℚ)) (c : ℂ) (x y : GeometricSource.CM.Vec ℂ) :
    GeometricSource.CM.localPairing E B.b τ (c • x) y = c * GeometricSource.CM.localPairing E B.b τ x y := by
  simp only [GeometricSource.CM.localPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem prescribed_forward (places : GeometricSource.CM.Places E) (d : Gal(E/ℚ) → Bool)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain)
    (w : GeometricSource.CM.Ambient E) (hw : GeometricSource.CM.prescribed E B places d z w) :
    GeometricSource.CM.prescribed E B places d (Frames.period E g z) (ComplexAction.CM.ambientOperator E g w) := by
  intro i
  have hi := hw i
  by_cases hid : i = places.distinguished
  · subst i
    simp only [places.identity, mul_one] at hi ⊢
    obtain ⟨c, hc, hline⟩ := Frames.line_action E g z hz
    constructor
    · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hi.1
      apply Submodule.mem_span_singleton.mpr
      refine ⟨a * c, ?_⟩
      rw [Frames.ambientOperator_apply, ← ha, map_smul, hline, smul_smul]
    · have hpair := (Frames.pairing_preserved E g 1 (GeometricSource.CM.BallDatum.lineVector z) (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))).trans hi.2
      rw [mul_one, hline, pairing_smul_left] at hpair
      exact (mul_eq_zero.mp hpair).resolve_left hc
  · rw [ite_eq_right hid] at hi ⊢
    split_ifs with hd
    · have hwzero : w (places.representative i) = 0 := by simpa only [ite_eq_left hd] using hi
      rw [Frames.ambientOperator_apply, hwzero, map_zero]
    · have hwzero : w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative i) = 0 := by
        simpa only [ite_eq_right hd] using hi
      rw [Frames.ambientOperator_apply, hwzero, map_zero]

theorem prescribed_equivariant (places : GeometricSource.CM.Places E) (d : Gal(E/ℚ) → Bool)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain)
    (w : GeometricSource.CM.Ambient E) :
    GeometricSource.CM.prescribed E B places d (Frames.period E g z) (ComplexAction.CM.ambientOperator E g w) ↔
      GeometricSource.CM.prescribed E B places d z w := by
  constructor
  · intro hw
    have h := prescribed_forward E places d g⁻¹ (Frames.period E g z)
      (period_preserves E g z hz) (ComplexAction.CM.ambientOperator E g w) hw
    rwa [period_inverse, ambient_inverse] at h
  · exact prescribed_forward E places d g z hz w

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PrescribedAction

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PeriodCovariance

/-! The actual source period matrix transforms by its constructed
rational symplectic action. This follows from the prescribed graph and
unitary equivariance, with no period-transformation hypothesis. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PrescribedAction

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem real_blocks_matrix (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) :
    Matrix.fromBlocks (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).complexify.A (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).complexify.B
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).complexify.C (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).complexify.D =
      g.val.map (algebraMap ℚ ℂ) := by
  ext i j
  cases i <;> cases j <;> exact Complex.ofReal_ratCast _

def graphPhase (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (x : I → ℂ) : (I ⊕ I) → ℂ :=
  Sum.elim (Z.matrix.mulVec x) x

theorem block_graph_action (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (x : I → ℂ) :
    (g.val.map (algebraMap ℚ ℂ)).mulVec (graphPhase Z x) =
      Sum.elim ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).complexify.numerator Z.matrix |>.mulVec x)
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).complexify.denominator Z.matrix |>.mulVec x) := by
  rw [← real_blocks_matrix, Matrix.fromBlocks_mulVec]
  simp only [graphPhase, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, Matrix.add_mulVec,
    Matrix.mulVec_mulVec]

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem complexFrame_graph (z : GeometricSource.CM.BallChart) (x : GeometricSource.CM.Positions E places → ℂ) :
    ComplexAction.CM.complexFrame E L.coordinates (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z) x) =
      graphPhase (L.period z) x := by
  change (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm
    (L.coordinates.complex (L.coordinates.complex.symm ((L.period z).matrix.mulVec x, x))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem graph_prescribed (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : GeometricSource.CM.Positions E places → ℂ) :
    GeometricSource.CM.prescribed E B places d z (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z) x) := by
  apply (L.graph_prescribed z hz _).mpr
  change (L.coordinates.complex (L.coordinates.complex.symm ((L.period z).matrix.mulVec x, x))).1 =
    (L.period z).matrix.mulVec
      (L.coordinates.complex (L.coordinates.complex.symm ((L.period z).matrix.mulVec x, x))).2
  rw [LinearEquiv.apply_symm_apply]

theorem transformed_graph (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : GeometricSource.CM.Positions E places → ℂ) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).complexify.numerator (L.period z).matrix).mulVec x =
      (L.period (Frames.period E g z)).matrix.mulVec
        (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).complexify.denominator (L.period z).matrix).mulVec x) := by
  let w := GeometricSource.CM.graphInAmbient E L.coordinates (L.period z) x
  let w' := ComplexAction.CM.ambientOperator E g w
  have hp : GeometricSource.CM.prescribed E B places d (Frames.period E g z) w' :=
    PrescribedAction.prescribed_forward E places d g z hz w (PeriodCovariance.graph_prescribed E L z hz x)
  have hgraph := (L.graph_prescribed (Frames.period E g z) (PrescribedAction.period_preserves E g z hz) w').mp hp
  have he :
      Sum.elim
        (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).complexify.numerator (L.period z).matrix).mulVec x)
        (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).complexify.denominator (L.period z).matrix).mulVec x) =
      ComplexAction.CM.complexFrame E L.coordinates w' := by
    rw [← block_graph_action, ← complexFrame_graph E L z x]
    exact ComplexAction.CM.complex_matrix_frame E L.coordinates g w
  have hu := congrArg (fun p : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℂ =>
    fun i => p (.inl i)) he
  have hl := congrArg (fun p : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℂ =>
    fun i => p (.inr i)) he
  exact hu.trans (hgraph.trans (congrArg (L.period (Frames.period E g z)).matrix.mulVec hl.symm))

theorem period_covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    L.period (Frames.period E g z) = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).transformSiegel (L.period z) := by
  let G := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)
  have hm : G.complexify.numerator (L.period z).matrix =
      (L.period (Frames.period E g z)).matrix * G.complexify.denominator (L.period z).matrix := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec]
    exact transformed_graph E L g z hz x
  have he : (L.period (Frames.period E g z)).matrix = (G.transformSiegel (L.period z)).matrix := by
    change _ = G.complexify.numerator (L.period z).matrix *
      (G.complexify.denominator (L.period z).matrix)⁻¹
    rw [hm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (G.denominator_det_isUnit (L.period z)),
      Matrix.mul_one]
  generalize L.period (Frames.period E g z) = Z at he ⊢
  generalize G.transformSiegel (L.period z) = W at he ⊢
  cases Z
  cases W
  cases he
  rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PeriodCovariance

end

end OAI
