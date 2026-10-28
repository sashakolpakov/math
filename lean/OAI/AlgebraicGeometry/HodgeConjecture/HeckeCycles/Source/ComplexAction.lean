import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource
import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Complex Action -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

/-! The actual rational special-unitary group acts symplectically in
the source's specified rational coordinates. This constructs the matrix
used in rational theta automorphy, preserving the original group action. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable {I : Type*} [Fintype I] [DecidableEq I]

def pairing (x y : (I ⊕ I) → ℚ) : ℚ :=
  ∑ i, (x (.inl i) * y (.inr i) - y (.inl i) * x (.inr i))

theorem pairing_negJ (x y : (I ⊕ I) → ℚ) :
    pairing x y = -(Matrix.J I ℚ).toBilin' x y := by
  simp [pairing, Matrix.toBilin'_apply, Matrix.J, Fintype.sum_sum_type,
    Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib, mul_comm]
  ring

theorem matrix_symplectic (T : Matrix (I ⊕ I) (I ⊕ I) ℚ)
    (hT : ∀ x y, pairing (T.mulVec x) (T.mulVec y) = pairing x y) :
    T ∈ Matrix.symplecticGroup I ℚ := by
  apply SymplecticGroup.mem_iff'.mpr
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (Matrix.J I ℚ).toBilin' (T.mulVec x) (T.mulVec y) = (Matrix.J I ℚ).toBilin' x y
  have h := congrArg Neg.neg (hT x y)
  simpa only [pairing_negJ, neg_neg] using h

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def frame : GeometricSource.CM.Vec E ≃ₗ[ℚ] ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :=
  C.rational.trans (LinearEquiv.sumArrowLequivProdArrow
    (GeometricSource.CM.Positions E places) (GeometricSource.CM.Positions E places) ℚ ℚ).symm

theorem frame_pairing (x y : GeometricSource.CM.Vec E) :
    pairing (frame E C x) (frame E C y) =
      Algebra.trace ℚ E (C.delta * C.a * GeometricSource.CM.hermitian E B.b x y) :=
  (C.symplectic x y).symm

def rationalAction (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : GeometricSource.CM.Vec E ≃ₗ[ℚ] GeometricSource.CM.Vec E :=
  (Matrix.SpecialLinearGroup.toLin' g.val).restrictScalars ℚ

theorem rationalAction_preserves (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x y : GeometricSource.CM.Vec E) :
    GeometricSource.CM.hermitian E B.b (rationalAction E g x) (rationalAction E g y) = GeometricSource.CM.hermitian E B.b x y :=
  g.property x y

def phaseAction (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) ≃ₗ[ℚ]
      ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :=
  (frame E C).symm.trans ((rationalAction E g).trans (frame E C))

theorem phaseAction_preserves (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (x y : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :
    pairing (phaseAction E C g x) (phaseAction E C g y) = pairing x y := by
  change pairing (frame E C (rationalAction E g ((frame E C).symm x)))
    (frame E C (rationalAction E g ((frame E C).symm y))) = _
  rw [frame_pairing, rationalAction_preserves, ← frame_pairing]
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def symplectic (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ :=
  ⟨LinearMap.toMatrix' (phaseAction E C g).toLinearMap,
    matrix_symplectic _ (by
      intro x y
      simpa only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] using
        phaseAction_preserves E C g x y)⟩

theorem symplectic_apply (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    (Symplectic.symplectic E C g).val.mulVec (frame E C x) = frame E C (rationalAction E g x) := by
  rw [Symplectic.symplectic, LinearMap.toMatrix'_mulVec]
  change frame E C (rationalAction E g ((frame E C).symm (frame E C x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem rationalAction_one :
    rationalAction E (1 : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) = LinearEquiv.refl ℚ (GeometricSource.CM.Vec E) := by
  apply LinearEquiv.ext
  intro x
  change Matrix.SpecialLinearGroup.toLin' (1 : Matrix.SpecialLinearGroup (Fin 3) E) x = x
  rw [map_one]
  rfl

theorem rationalAction_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    rationalAction E (g * h) = rationalAction E g * rationalAction E h := by
  apply LinearEquiv.ext
  intro x
  change Matrix.SpecialLinearGroup.toLin' (g.val * h.val) x =
    Matrix.SpecialLinearGroup.toLin' g.val (Matrix.SpecialLinearGroup.toLin' h.val x)
  rw [map_mul, LinearEquiv.mul_apply]

theorem phaseAction_one :
    phaseAction E C (1 : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) =
      LinearEquiv.refl ℚ ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) := by
  apply LinearEquiv.ext
  intro x
  change frame E C (rationalAction E 1 ((frame E C).symm x)) = x
  rw [rationalAction_one]
  exact (frame E C).apply_symm_apply x

theorem phaseAction_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    phaseAction E C (g * h) = phaseAction E C g * phaseAction E C h := by
  apply LinearEquiv.ext
  intro x
  change frame E C (rationalAction E (g * h) ((frame E C).symm x)) =
    frame E C (rationalAction E g ((frame E C).symm
      (frame E C (rationalAction E h ((frame E C).symm x)))))
  rw [LinearEquiv.symm_apply_apply, rationalAction_mul, LinearEquiv.mul_apply]

theorem symplectic_one : Symplectic.symplectic E C (1 : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) = 1 := by
  apply Subtype.ext
  change LinearMap.toMatrix' (phaseAction E C 1).toLinearMap = 1
  rw [phaseAction_one]
  exact LinearMap.toMatrix'_id

theorem symplectic_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    Symplectic.symplectic E C (g * h) = Symplectic.symplectic E C g * Symplectic.symplectic E C h := by
  apply Subtype.ext
  change LinearMap.toMatrix' (phaseAction E C (g * h)).toLinearMap =
    LinearMap.toMatrix' (phaseAction E C g).toLinearMap *
      LinearMap.toMatrix' (phaseAction E C h).toLinearMap
  rw [phaseAction_mul]
  exact LinearMap.toMatrix'_comp _ _

def hom : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ where
  toFun := Symplectic.symplectic E C
  map_one' := symplectic_one E C
  map_mul' := symplectic_mul E C

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM

/-! The complexification of the constructed rational symplectic action
is the literal action on the original CM embedding coordinates. The
comparison is derived by testing the specified rational frame. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def complexFrame : GeometricSource.CM.Ambient E ≃ₗ[ℂ] ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℂ) :=
  C.complex.trans (LinearEquiv.sumArrowLequivProdArrow
    (GeometricSource.CM.Positions E places) (GeometricSource.CM.Positions E places) ℂ ℂ).symm

theorem complexFrame_rational (x : GeometricSource.CM.Vec E) :
    complexFrame E C (GeometricSource.CM.embeddingCoordinates E x) = fun i => (Symplectic.frame E C x i : ℂ) := by
  funext i
  cases i with
  | inl i => exact congrFun (congrArg Prod.fst (C.extends_rational x)) i
  | inr i => exact congrFun (congrArg Prod.snd (C.extends_rational x)) i

theorem complexFrame_symm_rational (x : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :
    (complexFrame E C).symm (fun i => (x i : ℂ)) =
      GeometricSource.CM.embeddingCoordinates E ((Symplectic.frame E C).symm x) := by
  apply (complexFrame E C).injective
  rw [LinearEquiv.apply_symm_apply, complexFrame_rational, LinearEquiv.apply_symm_apply]

def ambientOperator (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : Module.End ℂ (GeometricSource.CM.Ambient E) :=
  LinearMap.pi (fun τ : Gal(E/ℚ) =>
    (Matrix.toLin' ((g.val : Matrix (Fin 3) (Fin 3) E).map
      (E.val.toRingHom.comp τ.toRingHom))).comp (LinearMap.proj τ))

theorem ambientOperator_rational (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    ambientOperator E g (GeometricSource.CM.embeddingCoordinates E x) =
      GeometricSource.CM.embeddingCoordinates E (Symplectic.rationalAction E g x) := by
  funext τ i
  exact (RingHom.map_mulVec (E.val.toRingHom.comp τ.toRingHom)
    (g.val : Matrix (Fin 3) (Fin 3) E) x i).symm

theorem rational_matrix_frame (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    ((Symplectic.symplectic E C g).val.map (algebraMap ℚ ℂ)).mulVec
        (complexFrame E C (GeometricSource.CM.embeddingCoordinates E x)) =
      complexFrame E C (ambientOperator E g (GeometricSource.CM.embeddingCoordinates E x)) := by
  rw [complexFrame_rational, ambientOperator_rational, complexFrame_rational]
  funext i
  exact (RingHom.map_mulVec (algebraMap ℚ ℂ) (Symplectic.symplectic E C g).val (Symplectic.frame E C x) i).symm.trans
    (congrArg (algebraMap ℚ ℂ) (congrFun (Symplectic.symplectic_apply E C g x) i))

theorem complex_matrix_frame (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Ambient E) :
    ((Symplectic.symplectic E C g).val.map (algebraMap ℚ ℂ)).mulVec (complexFrame E C x) =
      complexFrame E C (ambientOperator E g x) := by
  let T := Matrix.toLin' ((Symplectic.symplectic E C g).val.map (algebraMap ℚ ℂ))
  let U := (complexFrame E C).toLinearMap.comp
    ((ambientOperator E g).comp (complexFrame E C).symm.toLinearMap)
  have hTU : T = U := by
    apply (Pi.basisFun ℂ (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places)).ext
    intro i
    have hs : (Pi.single i (1 : ℂ) : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℂ) =
        fun k => ((Pi.single i (1 : ℚ) : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) k : ℂ) := by
      funext k
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    simp only [Pi.basisFun_apply]
    rw [hs]
    change ((Symplectic.symplectic E C g).val.map (algebraMap ℚ ℂ)).mulVec _ =
      complexFrame E C (ambientOperator E g ((complexFrame E C).symm _))
    rw [complexFrame_symm_rational]
    simpa only [complexFrame_rational, LinearEquiv.apply_symm_apply] using
      rational_matrix_frame E C g ((Symplectic.frame E C).symm (Pi.single i 1))
  have h := LinearMap.congr_fun hTU (complexFrame E C x)
  change _ = complexFrame E C (ambientOperator E g ((complexFrame E C).symm (complexFrame E C x))) at h
  rwa [LinearEquiv.symm_apply_apply] at h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM

end

end OAI
