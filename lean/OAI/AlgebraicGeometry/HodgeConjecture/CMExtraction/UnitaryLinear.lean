import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientConjugation

/-! # Unitary Linear -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryLinear.Approximation

noncomputable section

section

/-! Convert determinant-one unitary matrices to the exact linear group
used by the PEL datum. The map preserves every matrix entry. -/

open scoped Classical

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv.Quadratic OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientConjugation.TestTransport

variable {R : Type*} [CommRing R] [StarRing R] (b : R)

def unitaryMatrixSL : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm b) →* Matrix.SpecialLinearGroup (Fin 3) R where
  toFun g := ⟨g.val.val, congrArg Units.val g.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def unitaryMatrixLinear : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm b) →*
    AbelianModuli.ReferenceFamily.Groups.specialUnitarySubgroup (R := R) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd R) b) where
  toFun g := ⟨Matrix.SpecialLinearGroup.toLin' (unitaryMatrixSL b g),
    (UnitaryMatrixEquiv.Quadratic.unitary_matrix_iff b (unitaryMatrixSL b g)).mpr g.property.1, by
      apply Units.ext
      rw [LinearEquiv.coe_det, Units.val_one]
      change LinearMap.det (Matrix.toLin' g.val.val) = 1
      rw [LinearMap.det_toLin']
      exact congrArg Units.val g.property.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Matrix.SpecialLinearGroup.toLin'.comp (unitaryMatrixSL b))
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (Matrix.SpecialLinearGroup.toLin'.comp (unitaryMatrixSL b)) g h

theorem unitaryMatrixLinear_entry (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm b)) (i j : Fin 3) :
    (unitaryMatrixLinear b g).val (Pi.single j 1) i = g.val.val i j := by
  change (g.val.val.mulVec (Pi.single j 1)) i = g.val.val i j
  simp [Matrix.mulVec_single]

variable (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]

theorem finiteHermitian_eq_form (a : E) :
    AbelianModuli.ReferenceFamily.AdelicData.finiteHermitian E a = Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E))
      (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E a) := rfl

variable {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def matrixPELUnitary : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b)) →*
    P.FiniteSpecialUnitary := unitaryMatrixLinear (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b)

theorem matrixPELUnitary_entry
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b))) (i j : Fin 3) :
    (matrixPELUnitary E P g).val (Pi.single j 1) i = g.val.val i j :=
  unitaryMatrixLinear_entry (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b) g i j

theorem matrixPELUnitary_continuous : Continuous (matrixPELUnitary E P) := by
  apply continuous_induced_rng.mpr
  have hm : Continuous (fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b)) =>
      (g.val.val : Matrix (Fin 3) (Fin 3) (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E))) :=
    Units.continuous_val.comp continuous_subtype_val
  exact hm.congr (fun g => by
    funext i j
    exact (matrixPELUnitary_entry E P g i j).symm)

def matrixPELUnitaryContinuous : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b)) →ₜ*
    P.FiniteSpecialUnitary := ⟨matrixPELUnitary E P, matrixPELUnitary_continuous E P⟩

end

section

/-! The matrix-to-linear PEL map is bijective. Its inverse is the actual
matrix of the given linear equivalence in the standard basis. -/

open scoped Classical

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv.Quadratic OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientConjugation.TestTransport

variable {R : Type*} [CommRing R] [StarRing R] (b : R)

theorem unitaryMatrixLinear_bijective : Function.Bijective (unitaryMatrixLinear b) := by
  constructor
  · intro g h he
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact (unitaryMatrixLinear_entry b g i j).symm.trans
      ((congrArg (fun z : AbelianModuli.ReferenceFamily.Groups.specialUnitarySubgroup (R := R) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd R) b) =>
        z.val (Pi.single j 1) i) he).trans (unitaryMatrixLinear_entry b h i j))
  · intro g
    have hd : (LinearMap.toMatrix' g.val.toLinearMap).det = 1 := by
      rw [LinearMap.det_toMatrix', ← LinearEquiv.coe_det]
      exact congrArg Units.val g.property.2
    let A : Matrix.SpecialLinearGroup (Fin 3) R := ⟨LinearMap.toMatrix' g.val.toLinearMap, hd⟩
    have hA : Matrix.SpecialLinearGroup.toLin' A = g.val := by
      apply LinearEquiv.toLinearMap_injective
      exact Matrix.toLin'_toMatrix' g.val.toLinearMap
    have hU : A ∈ Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (starRingEnd R) b := by
      intro x y
      change Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd R) b (Matrix.SpecialLinearGroup.toLin' A x)
        (Matrix.SpecialLinearGroup.toLin' A y) = _
      rw [hA]
      exact g.property.1 x y
    let m : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm b) := ⟨Matrix.SpecialLinearGroup.toGL A,
      (UnitaryMatrixEquiv.Quadratic.unitary_matrix_iff b A).mp hU, by
        apply Units.ext
        exact hd⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    exact hA

def unitaryMatrixLinearEquiv : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm b) ≃*
    AbelianModuli.ReferenceFamily.Groups.specialUnitarySubgroup (R := R) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd R) b) :=
  MulEquiv.ofBijective (unitaryMatrixLinear b) (unitaryMatrixLinear_bijective b)

theorem unitaryMatrixLinearEquiv_symm_matrix
    (g : AbelianModuli.ReferenceFamily.Groups.specialUnitarySubgroup (R := R) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd R) b)) :
    ((unitaryMatrixLinearEquiv b).symm g).val.val = LinearMap.toMatrix' g.val.toLinearMap := by
  apply Matrix.ext
  intro i j
  have h := congrArg (fun z : AbelianModuli.ReferenceFamily.Groups.specialUnitarySubgroup (R := R) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd R) b) =>
      z.val (Pi.single j 1) i) ((unitaryMatrixLinearEquiv b).apply_symm_apply g)
  exact (unitaryMatrixLinear_entry b ((unitaryMatrixLinearEquiv b).symm g) i j).symm.trans h

variable (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def matrixPELUnitaryEquiv : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b)) ≃*
    P.FiniteSpecialUnitary := unitaryMatrixLinearEquiv (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b)

end

/-! The exact PEL linear group and its unitary matrices have the same
topology. Determinant one makes the inverse matrix its adjugate. -/

open scoped Classical

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv.Quadratic OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientConjugation.TestTransport

theorem unitaryMatrix_inverse_eq_adjugate {R : Type*} [CommRing R] [StarRing R]
    (b : R) (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm b)) : g.val.inv = g.val.val.adjugate := by
  have h : Matrix.SpecialLinearGroup.toGL (unitaryMatrixSL b g) = g.val := Units.ext rfl
  exact (congrArg Units.inv h).symm

variable (E : Type) [Field E] [NumberField E]

instance finiteCoefficientTopologicalRing : IsTopologicalRing (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) where
  continuous_add := continuous_add
  continuous_neg := continuous_neg
  continuous_mul := Finite.CoefficientTopology.TestTransport.finiteCoefficient_mul_continuous E

variable [NumberField.IsCMField E] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

theorem matrixPELUnitaryEquiv_symm_continuous : Continuous (matrixPELUnitaryEquiv E P).symm := by
  have hm : Continuous (fun g : P.FiniteSpecialUnitary => LinearMap.toMatrix' g.val.toLinearMap) :=
    continuous_induced_dom
  have hm' : Continuous (fun g : P.FiniteSpecialUnitary =>
      (((matrixPELUnitaryEquiv E P).symm g).val.val : Matrix (Fin 3) (Fin 3) (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E))) :=
    hm.congr (fun g => (unitaryMatrixLinearEquiv_symm_matrix (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b) g).symm)
  have hi : Continuous (fun g : P.FiniteSpecialUnitary =>
      (((matrixPELUnitaryEquiv E P).symm g).val.inv : Matrix (Fin 3) (Fin 3) (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E))) :=
    hm'.matrix_adjugate.congr (fun g =>
      (unitaryMatrix_inverse_eq_adjugate _ ((matrixPELUnitaryEquiv E P).symm g)).symm)
  have hu : Continuous (fun g : P.FiniteSpecialUnitary => ((matrixPELUnitaryEquiv E P).symm g).val) :=
    Units.continuous_iff.mpr ⟨hm', hi⟩
  exact hu.subtype_mk _

def matrixPELUnitaryHomeomorph : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E P.b)) ≃ₜ*
    P.FiniteSpecialUnitary where
  __ := matrixPELUnitaryEquiv E P
  continuous_toFun := matrixPELUnitary_continuous E P
  continuous_invFun := matrixPELUnitaryEquiv_symm_continuous E P

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryLinear.Approximation
