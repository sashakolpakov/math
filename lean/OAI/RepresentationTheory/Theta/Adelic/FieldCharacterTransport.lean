import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport
import OAI.RepresentationTheory.Theta.Adelic.FixedDeterminant

/-! # Field Character Transport -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.FieldCharacterTransport.Unitary

/-! Transport of native quadratic form matrices, units, characters, and
unitary groups along an actual topological field equivalence. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

section Algebra
variable {k l : Type} [Field k] [Field l] (e : k ≃+* l) (d : k)
variable {I : Type} [Fintype I] [DecidableEq I]

def fieldForm (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d)) :=
  A.map (QuadraticNormTransport.quadraticEquiv e d).toRingHom

def fieldFormUnit (A : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d)))ˣ :=
  Units.map (QuadraticNormTransport.quadraticEquiv e d).toRingHom.mapMatrix.toMonoidHom A

def fieldQuadraticUnits : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →* (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d))ˣ :=
  Units.map (QuadraticNormTransport.quadraticEquiv e d).toMonoidHom

theorem fieldQuadraticUnits_scalar (a : kˣ) :
    fieldQuadraticUnits e d (QuadraticNormSquareQuotient.scalarUnits d a) =
      QuadraticNormSquareQuotient.scalarUnits (e d) (Units.map e.toMonoidHom a) := by
  apply Units.ext
  ext <;> simp [fieldQuadraticUnits, QuadraticNormSquareQuotient.scalarUnits, QuadraticNormTransport.quadraticEquiv, Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange]

theorem fieldQuadraticUnits_delta (hd : d ≠ 0) :
    fieldQuadraticUnits e d (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) = Weil.AdelicSplitting.Normalization.Construction.deltaUnit (e d) ((map_ne_zero e).mpr hd) := by
  apply Units.ext
  ext <;> simp [fieldQuadraticUnits, QuadraticNormTransport.quadraticEquiv, Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange, Weil.AdelicSplitting.Normalization.Construction.deltaUnit]

theorem fieldFormUnit_det (A : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    Matrix.GeneralLinearGroup.det (fieldFormUnit e d A) =
      fieldQuadraticUnits e d (Matrix.GeneralLinearGroup.det A) := by
  apply Units.ext
  exact ((QuadraticNormTransport.quadraticEquiv e d).toRingHom.map_det A.val).symm

omit [Fintype I] [DecidableEq I] in
theorem fieldForm_hermitian (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (hA : A.conjTranspose = A) :
    (fieldForm e d A).conjTranspose = fieldForm e d A := by
  exact (Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose (QuadraticNormTransport.quadraticEquiv e d).toRingHom
    (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star e.toRingHom d) A).symm.trans (congrArg (fieldForm e d) hA)

theorem fieldForm_skew (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (hA : A.conjTranspose = -A) :
    (fieldForm e d A).conjTranspose = -(fieldForm e d A) := by
  exact (Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose (QuadraticNormTransport.quadraticEquiv e d).toRingHom
    (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star e.toRingHom d) A).symm.trans
      ((congrArg (fieldForm e d) hA).trans (map_neg (QuadraticNormTransport.quadraticEquiv e d).toRingHom.mapMatrix A))

def fieldUnitaryMap (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary A →* Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (fieldForm e d A) :=
  Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange (QuadraticNormTransport.quadraticEquiv e d).toRingHom (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star e.toRingHom d) A

theorem fieldUnitaryMap_difference (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary A) (u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hu : u.val = g.val.val - 1) :
    (fieldFormUnit e d u).val = (fieldUnitaryMap e d A g).val.val - 1 := by
  change (QuadraticNormTransport.quadraticEquiv e d).toRingHom.mapMatrix u.val =
    (QuadraticNormTransport.quadraticEquiv e d).toRingHom.mapMatrix g.val.val - 1
  rw [hu, map_sub, map_one]

end Algebra

variable {k l : Type} [NormedField k] [NormedField l]
variable (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (d : k)
variable {I : Type} [Fintype I] [DecidableEq I]

def fieldQuadraticHomeomorph : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d ≃ₜ Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d) where
  toEquiv := (QuadraticNormTransport.quadraticEquiv e d).toEquiv
  continuous_toFun := Weil.AdelicSplitting.QuadraticTopology.Construction.quadraticBaseChange_continuous e.toRingHom he d
  continuous_invFun := by
    rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
    exact ⟨hi.comp (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re (e d)), hi.comp (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im (e d))⟩

def fieldQuadraticUnitsContinuous : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d))ˣ :=
  ⟨fieldQuadraticUnits e d, (Weil.AdelicSplitting.QuadraticTopology.Construction.quadraticBaseChange_continuous e.toRingHom he d).units_map _⟩

def fieldQuadraticUnitsInverseContinuous : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d))ˣ →ₜ* (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ :=
  ⟨Units.map (QuadraticNormTransport.quadraticEquiv e d).symm.toMonoidHom, (fieldQuadraticHomeomorph e he hi d).symm.continuous.units_map _⟩

include he in
theorem fieldUnitaryMap_continuous (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) :
    Continuous (fieldUnitaryMap e d A) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro i <;> apply continuous_pi <;> intro j
  · exact (Weil.AdelicSplitting.QuadraticTopology.Construction.quadraticBaseChange_continuous e.toRingHom he d).comp
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((Units.continuous_val (M := Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))).comp continuous_subtype_val)))
  · exact (Weil.AdelicSplitting.QuadraticTopology.Construction.quadraticBaseChange_continuous e.toRingHom he d).comp
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((Units.continuous_coe_inv (M := Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))).comp continuous_subtype_val)))

def fieldUnitaryContinuous (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary A →ₜ* Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (fieldForm e d A) :=
  ⟨fieldUnitaryMap e d A, fieldUnitaryMap_continuous e he d A⟩

end RepresentationTheory.Theta.Adelic.FieldCharacterTransport.Unitary

namespace RepresentationTheory.Theta.Adelic.FieldCharacterTransport

/-! Prescribed multiplicative characters and their norm restrictions
transport through the native quadratic coefficient equivalence. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.FieldCharacterTransport.Unitary

variable {k l : Type} [NormedField k] [NormedField l]
variable (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (d : k)

def fieldMultiplicativeCharacter (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle) : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d))ˣ →ₜ* Circle :=
  χ.comp (Unitary.fieldQuadraticUnitsInverseContinuous e he hi d)

theorem fieldMultiplicativeCharacter_apply (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle) (a : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) :
    fieldMultiplicativeCharacter e he hi d χ (Unitary.fieldQuadraticUnits e d a) = χ a := by
  change χ (Units.map (QuadraticNormTransport.quadraticEquiv e d).symm.toMonoidHom (Units.map (QuadraticNormTransport.quadraticEquiv e d).toMonoidHom a)) = χ a
  congr 1
  apply Units.ext
  exact (QuadraticNormTransport.quadraticEquiv e d).symm_apply_apply a.val

theorem fieldMultiplicativeCharacter_restriction (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle) (r : ℕ)
    (hχ : ∀ a : kˣ, χ (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ r) (b : lˣ) :
    fieldMultiplicativeCharacter e he hi d χ (QuadraticNormSquareQuotient.scalarUnits (e d) b) = QuadraticNormCharacter.normSign (e d) b ^ r := by
  let a := Units.map e.symm.toMonoidHom b
  have ha : Units.map e.toMonoidHom a = b := by
    apply Units.ext
    exact e.apply_symm_apply b.val
  have hs := Unitary.fieldQuadraticUnits_scalar e d a
  rw [ha] at hs
  rw [← hs, fieldMultiplicativeCharacter_apply, hχ]
  have hn := QuadraticNormTransport.normSign_map e d a
  rw [ha] at hn
  exact congrArg (fun z : Circle => z ^ r) hn.symm

end RepresentationTheory.Theta.Adelic.FieldCharacterTransport

end

end OAI
