import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Geometric Group -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.GeometricGroup

/-! The actual archimedean special-unitary group acts on the ball
through the given orthonormal basis at the distinguished place. -/

open _root_.Matrix
open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural

section Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem conjugated_isometry (M M₀ G : Matrix I I ℂ) (B : (Matrix I I ℂ)ˣ)
    (hB : B.val.conjTranspose * M * B.val = M₀) (hG : G.conjTranspose * M * G = M) :
    (B.inv * G * B.val).conjTranspose * M₀ * (B.inv * G * B.val) = M₀ := by
  have hm : B.inv.conjTranspose * M₀ * B.inv = M := by
    rw [← hB]
    calc
      _ = (B.inv.conjTranspose * B.val.conjTranspose) * M * (B.val * B.inv) := by noncomm_ring
      _ = M := by rw [← Matrix.conjTranspose_mul, B.val_inv, Matrix.conjTranspose_one, one_mul, mul_one]
  calc
    _ = B.val.conjTranspose * (G.conjTranspose * (B.inv.conjTranspose * M₀ * B.inv) * G) * B.val := by
      simp only [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = M₀ := by rw [hm, hG, hB]

end Matrix

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def standardUnit (v : Fin A.places) : RationalSU.ArchimedeanSU F H →* (Matrix (Fin 3) (Fin 3) ℂ)ˣ where
  toFun g := (A.basisV v)⁻¹ * Units.map (A.complex v).mapMatrix.toMonoidHom (g (A.enumerate v)).val * A.basisV v
  map_one' := by simp
  map_mul' g h := by
    change (A.basisV v)⁻¹ *
      Units.map (A.complex v).mapMatrix.toMonoidHom ((g (A.enumerate v)).val * (h (A.enumerate v)).val) * A.basisV v = _
    rw [map_mul]
    group

theorem standardUnit_val (v : Fin A.places) (g : RationalSU.ArchimedeanSU F H) :
    (standardUnit A v g).val = BallGeometryData.standardMatrix A g v := rfl

theorem standardUnit_determinant (v : Fin A.places) (g : RationalSU.ArchimedeanSU F H) :
    Matrix.GeneralLinearGroup.det (standardUnit A v g) = 1 := by
  let G : (Matrix (Fin 3) (Fin 3) ℂ)ˣ := Units.map (A.complex v).mapMatrix.toMonoidHom (g (A.enumerate v)).val
  have hg : Matrix.GeneralLinearGroup.det G = 1 := by
    apply Units.ext
    change ((A.complex v).mapMatrix (g (A.enumerate v)).val.val).det = 1
    have hmap : A.complex v (g (A.enumerate v)).val.val.det =
        ((A.complex v).mapMatrix (g (A.enumerate v)).val.val).det :=
      (A.complex v).map_det _
    have he : (g (A.enumerate v)).val.val.det = 1 := congrArg Units.val (g (A.enumerate v)).property.2
    exact hmap.symm.trans ((congrArg (A.complex v) he).trans (map_one (A.complex v)))
  change Matrix.GeneralLinearGroup.det ((A.basisV v)⁻¹ * G * A.basisV v) = 1
  rw [map_mul, map_mul, map_inv, hg, mul_one, inv_mul_cancel]

theorem standardUnit_isometry (v : Fin A.places) (g : RationalSU.ArchimedeanSU F H) :
    (standardUnit A v g).val.conjTranspose *
      Matrix.diagonal (fun i : Fin 3 => if v = A.distinguished ∧ i = 2 then (-1 : ℂ) else 1) *
        (standardUnit A v g).val =
      Matrix.diagonal (fun i : Fin 3 => if v = A.distinguished ∧ i = 2 then (-1 : ℂ) else 1) := by
  apply conjugated_isometry _ _ _ (A.basisV v) (A.formV v)
  have h := congrArg (A.complex v).mapMatrix (g (A.enumerate v)).property.1
  rw [map_mul, map_mul] at h
  change (g (A.enumerate v)).val.val.conjTranspose.map (A.complex v) *
    (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))).map (A.complex v) *
    (g (A.enumerate v)).val.val.map (A.complex v) =
    (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))).map (A.complex v) at h
  have he : (g (A.enumerate v)).val.val.conjTranspose.map (A.complex v) =
      ((g (A.enumerate v)).val.val.map (A.complex v)).conjTranspose :=
    Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose (A.complex v).toRingHom (A.complex_star v) _
  rw [he] at h
  exact h

theorem standardUnit_continuous (v : Fin A.places) : Continuous (standardUnit A v) := by
  have hm : Continuous ((A.complex v).mapMatrix :
      Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v))) → Matrix (Fin 3) (Fin 3) ℂ) := by
    exact continuous_pi fun i => continuous_pi fun j =>
      (A.complex_continuous v).comp ((continuous_apply j).comp (continuous_apply i))
  have hu : Continuous (Units.map (A.complex v).mapMatrix.toMonoidHom :
      (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v))))ˣ →
        (Matrix (Fin 3) (Fin 3) ℂ)ˣ) := hm.units_map _
  exact (continuous_const.mul (hu.comp (continuous_subtype_val.comp (continuous_apply (A.enumerate v))))).mul continuous_const

theorem distinguished_standard_form :
    Matrix.diagonal (fun i : Fin 3 => if A.distinguished = A.distinguished ∧ i = 2 then (-1 : ℂ) else 1) =
      BallNatural.standardForm.val := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [BallNatural.standardForm, Matrix.diagonal_apply, Fin.ext_iff]

def geometricBallMap : RationalSU.ArchimedeanSU F H →* BallNatural.BallGroup where
  toFun g := ⟨standardUnit A A.distinguished g, by
    constructor
    · have h := standardUnit_isometry A A.distinguished g
      rw [distinguished_standard_form] at h
      exact h
    · exact standardUnit_determinant A A.distinguished g⟩
  map_one' := Subtype.ext (map_one (standardUnit A A.distinguished))
  map_mul' g h := Subtype.ext (map_mul (standardUnit A A.distinguished) g h)

def geometricBallHom : RationalSU.ArchimedeanSU F H →ₜ* BallNatural.BallGroup :=
  ⟨geometricBallMap A, (standardUnit_continuous A A.distinguished).subtype_mk _⟩

theorem geometricBallHom_matrix (g : RationalSU.ArchimedeanSU F H) :
    (BallNatural.asSL (geometricBallHom A g)).val = BallGeometryData.standardMatrix A g A.distinguished := rfl

end RepresentationTheory.Theta.Adelic.GeometricGroup

namespace RepresentationTheory.Theta.Adelic.GeometricGroup.UnitaryDualAction

/-! An isometry of a diagonal Hermitian form acts on its Hermitian
dual by the actual inverse-transpose matrix. -/

open scoped Classical

open _root_.Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem unitary_conjugate_dual (U : (Matrix I I ℂ)ˣ) (S : Matrix I I ℂ)
    (hS : S.transpose = S) (hU : U.val.conjTranspose * S * U.val = S) :
    S * U.val.map star = U.inv.transpose * S := by
  have ht := congrArg Matrix.transpose hU
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hS, Matrix.conjTranspose_transpose] at ht
  have hi : U.inv.transpose * U.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, U.val_inv, Matrix.transpose_one]
  calc
    _ = (U.inv.transpose * U.val.transpose) * (S * U.val.map star) := by rw [hi, one_mul]
    _ = U.inv.transpose * (U.val.transpose * S * U.val.map star) := by noncomm_ring
    _ = _ := by rw [Matrix.mul_assoc U.val.transpose S (U.val.map star), ht]

theorem unitary_diagonal_dual (U : (Matrix I I ℂ)ˣ) (s : I → ℂ)
    (hU : U.val.conjTranspose * Matrix.diagonal s * U.val = Matrix.diagonal s)
    (x : I → ℂ) (c : ℂ) (i : I) :
    U.inv.transpose.mulVec (fun k => s k * c * star (x k)) i =
      s i * c * star (U.val.mulVec x i) := by
  have hd := unitary_conjugate_dual U (Matrix.diagonal s) (by simp) hU
  have hx : (Matrix.diagonal s).mulVec (fun k => star (U.val.mulVec x k)) =
      U.inv.transpose.mulVec ((Matrix.diagonal s).mulVec (fun k => star (x k))) := by
    rw [Weil.AdelicSplitting.TensorSpace.Construction.conjugate_mulVec, Matrix.mulVec_mulVec, hd, ← Matrix.mulVec_mulVec]
  have hc : (fun k => s k * c * star (x k)) =
      c • (Matrix.diagonal s).mulVec (fun k => star (x k)) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
    ring
  rw [hc, Matrix.mulVec_smul]
  change c * U.inv.transpose.mulVec ((Matrix.diagonal s).mulVec (fun k => star (x k))) i = _
  rw [← hx, Matrix.mulVec_diagonal]
  ring

end RepresentationTheory.Theta.Adelic.GeometricGroup.UnitaryDualAction

end

end OAI
