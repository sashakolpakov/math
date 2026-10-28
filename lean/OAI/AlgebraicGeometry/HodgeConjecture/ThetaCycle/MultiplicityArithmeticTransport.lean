import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicTensorComplexCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicReference

/-! # Multiplicity Arithmetic Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MultiplicityArithmeticTransport.CM

noncomputable section

section

/-! Transport an actual geometric multiplicity basis back to a fixed
rational skew-Hermitian space. This changes only the orthonormal basis
and retains every CM place, real/complex coordinate map, and Hodge sign. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W W' : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W')

def nativeRationalComplexCoordinate (v : Fin A.places) : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d →+* ℂ :=
  (A.complex v).toRingHom.comp (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)))

theorem native_rational_complex_coordinate_star (v : Fin A.places) (x : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) :
    nativeRationalComplexCoordinate A v (star x) = star (nativeRationalComplexCoordinate A v x) :=
  (congrArg (A.complex v) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v))) d x)).trans
    (A.complex_star v _)

def nativeComplexMultiplicityBasis
    (T : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ) (v : Fin A.places) :
    (Matrix (Fin m) (Fin m) ℂ)ˣ :=
  Units.map (nativeRationalComplexCoordinate A v).mapMatrix.toMonoidHom T

theorem native_complex_multiplicity_congruence
    (T : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hT : T.val.conjTranspose * W.val * T.val = W'.val) (v : Fin A.places) :
    (nativeComplexMultiplicityBasis A T v).val.conjTranspose *
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F W.val (.inl (A.enumerate v))).map (A.complex v) *
        (nativeComplexMultiplicityBasis A T v).val =
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F W'.val (.inl (A.enumerate v))).map (A.complex v) := by
  let f := nativeRationalComplexCoordinate A v
  have h := congrArg (fun M => M.map f) hT
  rw [Matrix.map_mul, Matrix.map_mul,
    Matrix.conjTranspose_map f (native_rational_complex_coordinate_star A v)] at h
  exact h

def transportMultiplicityArithmetic
    (T : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hT : T.val.conjTranspose * W.val * T.val = W'.val) : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W where
  places := A.places
  enumerate := A.enumerate
  distinguished := A.distinguished
  other_place := A.other_place
  real := A.real
  real_continuous := A.real_continuous
  real_inverse_continuous := A.real_inverse_continuous
  complex := A.complex
  complex_continuous := A.complex_continuous
  complex_inverse_continuous := A.complex_inverse_continuous
  complex_scalar := A.complex_scalar
  complex_star := A.complex_star
  basisV := A.basisV
  basisP v := nativeComplexMultiplicityBasis A T v * A.basisP v
  positive := A.positive
  distinguished_sign := A.distinguished_sign
  formV := A.formV
  formP v := by
    change ((nativeComplexMultiplicityBasis A T v).val * (A.basisP v).val).conjTranspose *
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F W.val (.inl (A.enumerate v))).map (A.complex v) *
        ((nativeComplexMultiplicityBasis A T v).val * (A.basisP v).val) = _
    rw [Matrix.conjTranspose_mul]
    calc
      _ = (A.basisP v).val.conjTranspose *
          ((nativeComplexMultiplicityBasis A T v).val.conjTranspose *
            (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F W.val (.inl (A.enumerate v))).map (A.complex v) *
              (nativeComplexMultiplicityBasis A T v).val) * (A.basisP v).val := by noncomm_ring
      _ = _ := by rw [native_complex_multiplicity_congruence A T hT v]; exact A.formP v

theorem transport_multiplicity_standard_matrix
    (T : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hT : T.val.conjTranspose * W.val * T.val = W'.val)
    (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix (transportMultiplicityArithmetic A T hT) g v = RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix A g v := rfl

theorem transport_multiplicity_geometric_frame
    (T : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hT : T.val.conjTranspose * W.val * T.val = W'.val)
    (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (u : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (transportMultiplicityArithmetic A T hT) z u = RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z u := rfl

theorem transport_multiplicity_rational_position
    (T : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hT : T.val.conjTranspose * W.val * T.val = W'.val) :
    RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates (transportMultiplicityArithmetic A T hT) =
      RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A := rfl

theorem transport_multiplicity_original_finite_input
    (T : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hT : T.val.conjTranspose * W.val * T.val = W'.val)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) :
    IntrinsicReference.CM.nativeOriginalFiniteInput (transportMultiplicityArithmetic A T hT) φ =
      IntrinsicReference.CM.nativeOriginalFiniteInput A φ := rfl

end

/-! The transported native tensor normalizer cancels the actual
multiplicity basis change, in both CM components. This identifies the
geometric tensors on the fixed space with the split-source frames. -/

open scoped Classical _root_.NumberField _root_.Matrix Kronecker
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W W' : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W')
  (T : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (hT : T.val.conjTranspose * W.val * T.val = W'.val)

def nativeMultiplicityTensorMatrix (v : Fin A.places) : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ :=
  (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (nativeComplexMultiplicityBasis A T v).val

theorem transport_multiplicity_normalizer_cancel (v : Fin A.places) :
    IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (transportMultiplicityArithmetic A T hT) v *
      nativeMultiplicityTensorMatrix A T v = IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer A v := by
  change ((A.basisV v).inv ⊗ₖ ((A.basisP v).inv * (nativeComplexMultiplicityBasis A T v).inv)) *
    ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (nativeComplexMultiplicityBasis A T v).val) =
      (A.basisV v).inv ⊗ₖ (A.basisP v).inv
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.mul_assoc,
    (nativeComplexMultiplicityBasis A T v).inv_val, Matrix.mul_one]

def nativeMultiplicityPhaseAction : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A →ₗ[ℂ] RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A where
  toFun w v :=
    ((nativeMultiplicityTensorMatrix A T v).mulVec (w v).1,
      ((nativeMultiplicityTensorMatrix A T v).map star).mulVec (w v).2)
  map_add' x y := by
    funext v
    apply Prod.ext
    · exact Matrix.mulVec_add (nativeMultiplicityTensorMatrix A T v) (x v).1 (y v).1
    · exact Matrix.mulVec_add ((nativeMultiplicityTensorMatrix A T v).map star) (x v).2 (y v).2
  map_smul' c x := by
    funext v
    apply Prod.ext
    · exact Matrix.mulVec_smul (nativeMultiplicityTensorMatrix A T v) c (x v).1
    · exact Matrix.mulVec_smul ((nativeMultiplicityTensorMatrix A T v).map star) c (x v).2

theorem transport_multiplicity_paired_components (w : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A) :
    IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (transportMultiplicityArithmetic A T hT)
      (nativeMultiplicityPhaseAction A T w) = IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents A w := by
  refine funext (fun v : Fin A.places => ?_)
  apply Prod.ext
  · change (IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (transportMultiplicityArithmetic A T hT) v).mulVec
      ((nativeMultiplicityTensorMatrix A T v).mulVec (w v).1) =
        (IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer A v).mulVec (w v).1
    rw [Matrix.mulVec_mulVec, transport_multiplicity_normalizer_cancel]
  · have he := congrArg (fun M : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ =>
      M.map (starRingEnd ℂ)) (transport_multiplicity_normalizer_cancel A T hT v)
    rw [Matrix.map_mul] at he
    funext ij
    change (if v = A.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
      (if A.positive v ij.2 then (1 : ℂ) else -1) *
        ((IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (transportMultiplicityArithmetic A T hT) v).map star).mulVec
          (((nativeMultiplicityTensorMatrix A T v).map star).mulVec (w v).2) ij =
      (if v = A.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
        (if A.positive v ij.2 then (1 : ℂ) else -1) *
          ((IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer A v).map star).mulVec (w v).2 ij
    exact congrArg (fun x : ℂ =>
      (if v = A.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
        (if A.positive v ij.2 then (1 : ℂ) else -1) * x)
      (congrFun ((Matrix.mulVec_mulVec _ _ _).trans
        (congrArg (fun M => M.mulVec (w v).2) he)) ij)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MultiplicityArithmeticTransport.CM
