import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import OAI.RepresentationTheory.Theta.Adelic.UnitaryConnected
import OAI.Geometry.ComplexBall.IntegralLattice
import OAI.Geometry.ComplexBall.RealPlaces
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnisotropicCocharacters

/-! # Arithmetic Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArithmeticModel.HermitianArithmetic

noncomputable section

/-! The special unitary group of an arbitrary rational Hermitian matrix
has its actual six-dimensional algebraic model over the maximal real
subfield. The coordinate equivalence preserves the original action.
The transpose below accounts for the linear-first convention in ReferenceFamily. -/

open scoped Classical
open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction _root_.NumberField

private theorem formValue_matrix_iff {R : Type*} [CommRing R] [StarRing R]
    (H A : Matrix (Fin 3) (Fin 3) R) :
    A.conjTranspose * H * A = H ↔
      ∀ x y, RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue H (A.mulVec x) (A.mulVec y) = RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue H x y := by
  constructor
  · intro h x y
    rw [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue_change, h]
  · intro h
    ext i j
    have hij := h (Pi.single i 1) (Pi.single j 1)
    rw [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue_change] at hij
    simpa [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite] using hij

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

abbrev QuadraticField := RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)

def quadraticMatrix (H : Matrix (Fin 3) (Fin 3) E) :
    Matrix (Fin 3) (Fin 3) (QuadraticField δ hδ) :=
  H.transpose.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm

def linearMatrixEquiv : (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) ≃*
    (Matrix (Fin 3) (Fin 3) (QuadraticField δ hδ))ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)).symm.trans
    (Matrix.GeneralLinearGroup.toLin.symm.trans
      (Units.mapEquiv (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm.toRingEquiv.mapMatrix.toMulEquiv))

theorem linearMatrixEquiv_matrix (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (linearMatrixEquiv δ hδ hδ0 g).val =
      (LinearMap.toMatrix' g.toLinearMap).map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm := rfl

theorem linearMatrixEquiv_action (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (x : Fin 3 → QuadraticField δ hδ) :
    (fun i => Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0
      ((linearMatrixEquiv δ hδ hδ0 g).val.mulVec x i)) =
        g (fun i => Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 (x i)) := by
  rw [linearMatrixEquiv_matrix]
  ext i
  have h := congrFun (LinearMap.congr_fun (Matrix.toLin'_toMatrix' g.toLinearMap)
    (fun i => Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 (x i))) i
  simpa only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.map_apply, AlgEquiv.apply_symm_apply, LinearEquiv.coe_coe] using h

theorem quadraticMatrix_pairing (H : Matrix (Fin 3) (Fin 3) E)
    (x y : Fin 3 → QuadraticField δ hδ) :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (quadraticMatrix δ hδ hδ0 H) x y) =
      Datum.RankThreePELDatum.matrixHermitian H
        (fun i => Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 (y i))
        (fun i => Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 (x i)) := by
  simp only [quadraticMatrix, RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec, dotProduct,
    Datum.RankThreePELDatum.matrixHermitian, map_sum, map_mul, Matrix.map_apply,
    Matrix.transpose_apply, AlgEquiv.apply_symm_apply, Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.quadraticEquiv_star,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem linearMatrixEquiv_unitary_iff (H : Matrix (Fin 3) (Fin 3) E)
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (linearMatrixEquiv δ hδ hδ0 g).val.conjTranspose * quadraticMatrix δ hδ hδ0 H *
      (linearMatrixEquiv δ hδ hδ0 g).val = quadraticMatrix δ hδ hδ0 H ↔
        ∀ x y, Datum.RankThreePELDatum.matrixHermitian H (g x) (g y) =
          Datum.RankThreePELDatum.matrixHermitian H x y := by
  rw [formValue_matrix_iff]
  constructor
  · intro hg x y
    have h := congrArg (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0)
      (hg (fun i => (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (y i))
        (fun i => (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (x i)))
    rw [quadraticMatrix_pairing, quadraticMatrix_pairing,
      linearMatrixEquiv_action, linearMatrixEquiv_action] at h
    simpa only [AlgEquiv.apply_symm_apply] using h
  · intro hg x y
    apply (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).injective
    rw [quadraticMatrix_pairing, quadraticMatrix_pairing,
      linearMatrixEquiv_action, linearMatrixEquiv_action]
    exact hg _ _

theorem linearMatrixEquiv_det_one_iff (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Matrix.GeneralLinearGroup.det (linearMatrixEquiv δ hδ hδ0 g) = 1 ↔
      LinearEquiv.det g = 1 := by
  rw [← Units.val_inj, ← Units.val_inj]
  simp only [LinearEquiv.coe_det, Units.val_one]
  change (linearMatrixEquiv δ hδ hδ0 g).val.det = 1 ↔ LinearMap.det g.toLinearMap = 1
  rw [linearMatrixEquiv_matrix]
  have hm : ((LinearMap.toMatrix' g.toLinearMap).map
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm).det =
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (LinearMap.toMatrix' g.toLinearMap).det :=
    ((Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm.toRingHom.map_det _).symm
  rw [hm, LinearMap.det_toMatrix']
  constructor
  · intro h
    apply (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm.injective
    simpa only [map_one] using h
  · intro h
    rw [h, map_one]

def specialUnitaryEquiv (H : Matrix (Fin 3) (Fin 3) E) :
    Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H) ≃*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (quadraticMatrix δ hδ hδ0 H) where
  toFun g := ⟨linearMatrixEquiv δ hδ hδ0 g.val,
    (linearMatrixEquiv_unitary_iff δ hδ hδ0 H g.val).mpr g.property.1,
    (linearMatrixEquiv_det_one_iff δ hδ hδ0 g.val).mpr g.property.2⟩
  invFun g := ⟨(linearMatrixEquiv δ hδ hδ0).symm g.val, by
    have hu := (linearMatrixEquiv_unitary_iff δ hδ hδ0 H
      ((linearMatrixEquiv δ hδ hδ0).symm g.val))
    have hd := (linearMatrixEquiv_det_one_iff δ hδ hδ0
      ((linearMatrixEquiv δ hδ hδ0).symm g.val))
    rw [MulEquiv.apply_symm_apply] at hu hd
    exact ⟨hu.mp g.property.1, hd.mp g.property.2⟩⟩
  left_inv g := Subtype.ext ((linearMatrixEquiv δ hδ hδ0).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((linearMatrixEquiv δ hδ hδ0).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext (map_mul (linearMatrixEquiv δ hδ hδ0) g.val h.val)

def algebraicGroup (H : Matrix (Fin 3) (Fin 3) E) :
    NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) 6 :=
  RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel.unitaryAlgebraicGroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)
    (quadraticMatrix δ hδ hδ0 H)

def rationalEquiv (H : Matrix (Fin 3) (Fin 3) E) :
    Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H) ≃*
      (algebraicGroup δ hδ hδ0 H).RationalPoints :=
  (specialUnitaryEquiv δ hδ hδ0 H).trans
    (RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel.regularUnitaryEquiv (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)
      (quadraticMatrix δ hδ hδ0 H))

theorem rationalEquiv_matrix (H : Matrix (Fin 3) (Fin 3) E)
    (g : Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)) :
    (rationalEquiv δ hδ hδ0 H g).val.val =
      Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)
        ((LinearMap.toMatrix' g.val.toLinearMap).map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm) := rfl

theorem rationalEquiv_action (H : Matrix (Fin 3) (Fin 3) E)
    (g : Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)) (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0 (g.val x) =
      Matrix.SpecialLinearGroup.toLin' (rationalEquiv δ hδ hδ0 H g).val
        (Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0 x) := by
  have hx := Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates_mulVec δ hδ hδ0 (LinearMap.toMatrix' g.val.toLinearMap) x
  change Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0 (g.val x) =
    (rationalEquiv δ hδ hδ0 H g).val.val.mulVec (Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0 x)
  rw [rationalEquiv_matrix]
  convert hx using 1
  exact congrArg (Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0)
    (LinearMap.congr_fun (Matrix.toLin'_toMatrix' g.val.toLinearMap) x).symm

def quadraticMatrixUnit (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0) :
    (Matrix (Fin 3) (Fin 3) (QuadraticField δ hδ))ˣ :=
  Units.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm.toRingHom.mapMatrix.toMonoidHom
    (Matrix.GeneralLinearGroup.mkOfDetNeZero H.transpose (by simpa using hH))

theorem quadraticMatrixUnit_val (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0) :
    (quadraticMatrixUnit δ hδ hδ0 H hH).val = quadraticMatrix δ hδ hδ0 H := rfl

theorem quadraticMatrix_hermitian (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) :
    (quadraticMatrix δ hδ hδ0 H).conjTranspose = quadraticMatrix δ hδ hδ0 H := by
  apply Matrix.ext
  intro i j
  apply (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).injective
  change Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0
      (star ((Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (H i j))) =
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 ((Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (H j i))
  rw [Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.quadraticEquiv_star, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact (hH j i).symm

include hδ0 in
theorem imaginarySquare_ne_zero : Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ ≠ 0 := by
  intro h
  have hpow : δ ^ 2 = 0 := congrArg Subtype.val h
  exact (pow_ne_zero 2 hδ0) hpow

def connectedGroup (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (hdet : H.det ≠ 0) :
    NumberTheory.ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) :=
  RepresentationTheory.Theta.Adelic.UnitaryConnected.connectedSemisimpleUnitaryGroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)
    (quadraticMatrixUnit δ hδ hδ0 H hdet) (imaginarySquare_ne_zero δ hδ hδ0)
    (quadraticMatrix_hermitian δ hδ hδ0 H hH)

theorem connectedGroup_matrix (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (hdet : H.det ≠ 0) :
    (connectedGroup δ hδ hδ0 H hH hdet).matrixGroup = algebraicGroup δ hδ hδ0 H := rfl

private theorem matrixHermitian_real_smul (H : Matrix (Fin 3) (Fin 3) E)
    (a : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Datum.RankThreePELDatum.matrixHermitian H ((a : E) • v) ((a : E) • v) =
      (a : E) ^ 2 * Datum.RankThreePELDatum.matrixHermitian H v v := by
  have ha := (IsCMField.complexConj_eq_self_iff E (a : E)).mpr a.property
  simp only [Datum.RankThreePELDatum.matrixHermitian, Pi.smul_apply, smul_eq_mul, map_mul, ha,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem connectedGroup_anisotropic (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (hdet : H.det ≠ 0)
    (han : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H v v = 0 → v = 0)
    (μ : E →+* ℂ) : NumberTheory.ArithmeticGroups.Lattices.Algebraic.IsAnisotropic (connectedGroup δ hδ hδ0 H hH hdet) := by
  let e := Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0
  let r := rationalEquiv δ hδ hδ0 H
  let G := algebraicGroup δ hδ hδ0 H
  let q : (Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) → E := fun v =>
    Datum.RankThreePELDatum.matrixHermitian H (e.symm v) (e.symm v)
  have hq (a : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) (v : Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) :
      q (a • v) = algebraMap (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) E a ^ 2 * q v := by
    change Datum.RankThreePELDatum.matrixHermitian H (e.symm (a • v)) (e.symm (a • v)) = _
    rw [map_smul]
    exact matrixHermitian_real_smul H a (e.symm v)
  have hzero (v : Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) (hv : q v = 0) : v = 0 := by
    apply e.symm.injective
    rw [map_zero]
    exact han (e.symm v) hv
  have hinv (g : G.RationalPoints) (v : Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) :
      q (Matrix.SpecialLinearGroup.toLin' g.val v) = q v := by
    have he : e.symm (Matrix.SpecialLinearGroup.toLin' g.val v) = (r.symm g).val (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply]
      have hc := rationalEquiv_action δ hδ hδ0 H (r.symm g) (e.symm v)
      change e ((r.symm g).val (e.symm v)) =
        Matrix.SpecialLinearGroup.toLin' (r (r.symm g)).val (e (e.symm v)) at hc
      rw [r.apply_symm_apply, e.apply_symm_apply] at hc
      exact hc.symm
    change Datum.RankThreePELDatum.matrixHermitian H (e.symm _) (e.symm _) =
      Datum.RankThreePELDatum.matrixHermitian H (e.symm v) (e.symm v)
    rw [he]
    exact (r.symm g).property.1 (e.symm v) (e.symm v)
  intro c K _ ι
  exact AnisotropicCocharacters.cocharacter_trivial_of_anisotropic_invariant G (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ)
    (algebraMap (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) E) q hq hzero hinv c K ι

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArithmeticModel.HermitianArithmetic
