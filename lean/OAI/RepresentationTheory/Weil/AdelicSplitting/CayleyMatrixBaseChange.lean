import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticMatrixCoordinates
import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticGenerators

/-! # Cayley Matrix Base Change -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyMatrixBaseChange.Construction

noncomputable section

section

/-! Rational matrix data for the Fourier expression of Cayley coefficients.
The difference matrix is retained as an actual unit, so field maps preserve
its inverse without an extra inverse-matrix premise. -/

open scoped Classical _root_.Matrix

variable (F : Type) [Field F] (N : ℕ)

abbrev PhaseMatrixUnit := (Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) F)ˣ

def phaseWeylUnit : PhaseMatrixUnit F N :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Weil.Local.Generators.Construction.weylSymplectic F N).val (by
    rw [SymplecticGroup.det_eq_one (Weil.Local.Generators.Construction.weylSymplectic F N).property]
    exact one_ne_zero)

def phaseUnitCoordinates (D : PhaseMatrixUnit F N) : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F (N + N) :=
  Units.map (Matrix.reindexRingEquiv F finSumFinEquiv).toMonoidHom D

def cayleyCoefficientLinear (D : PhaseMatrixUnit F N) : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F (N + N) :=
  (phaseUnitCoordinates F N (phaseWeylUnit F N * D⁻¹))⁻¹

variable [CharZero F]

def cayleyCoefficientQuadratic (D : PhaseMatrixUnit F N) : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix F (N + N) :=
  QuadraticMatrixCoordinates.Construction.symmetricPart (Matrix.reindex finSumFinEquiv finSumFinEquiv (D⁻¹.valᵀ * Matrix.J (Fin N) F))

theorem cayleyCoefficientQuadratic_apply (D : PhaseMatrixUnit F N) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (N + N)) :
    Weil.Local.FunctionsMetaplectic.Construction.quadratic (cayleyCoefficientQuadratic F N D).val x =
      (Matrix.J (Fin N) F).toBilin'
        (D⁻¹.val *ᵥ fun j => x (finSumFinEquiv j)) (fun j => x (finSumFinEquiv j)) / 2 := by
  rw [cayleyCoefficientQuadratic, QuadraticMatrixCoordinates.Construction.quadratic_symmetricPart, QuadraticMatrixCoordinates.Construction.reindex_toBilin,
    QuadraticMatrixCoordinates.Construction.toBilin_transpose_mul_left]

omit [CharZero F] in
theorem phaseUnitCoordinates_mulVec (D : PhaseMatrixUnit F N) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (N + N))
    (j : Fin N ⊕ Fin N) :
    ((phaseUnitCoordinates F N D).val *ᵥ x) (finSumFinEquiv j) =
      (D.val *ᵥ fun i => x (finSumFinEquiv i)) j := by
  change (∑ i : Fin (N + N), D.val (finSumFinEquiv.symm (finSumFinEquiv j)) (finSumFinEquiv.symm i) * x i) = _
  rw [finSumFinEquiv.symm_apply_apply,
    ← finSumFinEquiv.sum_comp (fun i => D.val j (finSumFinEquiv.symm i) * x i)]
  simp only [finSumFinEquiv.symm_apply_apply]
  rfl

omit [CharZero F] in
theorem cayleyCoefficientLinear_inverse (D : PhaseMatrixUnit F N) :
    (cayleyCoefficientLinear F N D)⁻¹ = phaseUnitCoordinates F N (phaseWeylUnit F N * D⁻¹) := inv_inv _

variable {k : Type} [NormedField k] [CharZero k]

omit [CharZero k] in
theorem openCellDifference_inverse_unit (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (D : PhaseMatrixUnit k N) (hD : D.val = g.val - 1) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    (SchrodingerPairing.Construction.openCellDifference k N g hg).symm x = D⁻¹.val *ᵥ x := by
  apply (SchrodingerPairing.Construction.openCellDifference k N g hg).injective
  rw [(SchrodingerPairing.Construction.openCellDifference k N g hg).apply_symm_apply]
  change x = (g.val - 1) *ᵥ (D⁻¹.val *ᵥ x)
  rw [← hD, Matrix.mulVec_mulVec]
  change x = (D.val * D.inv) *ᵥ x
  rw [D.val_inv, Matrix.one_mulVec]

theorem cayleyCoefficientQuadratic_local (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (D : PhaseMatrixUnit k N) (hD : D.val = g.val - 1) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k (N + N)) :
    Weil.Local.FunctionsMetaplectic.Construction.quadratic (cayleyCoefficientQuadratic k N D).val x =
      SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg ((PhaseMeasure.Construction.phaseCoordinates k N).symm x) := by
  rw [cayleyCoefficientQuadratic_apply, SchrodingerPairing.Construction.schrodingerCayleyPhase,
    UnitarySplitting.CayleyCompositionPhase.Construction.cayleyWeylPhase, openCellDifference_inverse_unit N g hg D hD]
  rfl

omit [CharZero k] in
theorem cayleyCoefficientLinear_local (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (D : PhaseMatrixUnit k N) (hD : D.val = g.val - 1) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k (N + N)) :
    (cayleyCoefficientLinear k N D)⁻¹.val *ᵥ x =
      PhaseMeasure.Construction.phaseCoordinates k N (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.weylSymplectic k N)
        ((SchrodingerPairing.Construction.openCellDifference k N g hg).symm ((PhaseMeasure.Construction.phaseCoordinates k N).symm x))) := by
  rw [cayleyCoefficientLinear_inverse, openCellDifference_inverse_unit N g hg D hD]
  funext i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rw [phaseUnitCoordinates_mulVec]
  have he := Homeomorph.piCongrLeft_apply_apply
    (Y := fun _ : Fin (N + N) => k) finSumFinEquiv
    (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.weylSymplectic k N) (D⁻¹.val *ᵥ (PhaseMeasure.Construction.phaseCoordinates k N).symm x)) j
  rw [show PhaseMeasure.Construction.phaseCoordinates k N
      (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.weylSymplectic k N) (D⁻¹.val *ᵥ (PhaseMeasure.Construction.phaseCoordinates k N).symm x))
        (finSumFinEquiv j) =
      Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.weylSymplectic k N) (D⁻¹.val *ᵥ (PhaseMeasure.Construction.phaseCoordinates k N).symm x) j from he]
  change (((Weil.Local.Generators.Construction.weylSymplectic k N).val * D⁻¹.val) *ᵥ fun i => x (finSumFinEquiv i)) j = _
  rw [← Matrix.mulVec_mulVec]
  rfl

end

/-! The Cayley coefficient matrix data commutes with field embeddings. -/

open scoped Classical _root_.Matrix

variable {F k : Type} [Field F] [Field k] (N : ℕ) (e : F →+* k)

def mapPhaseMatrixUnit (D : PhaseMatrixUnit F N) : PhaseMatrixUnit k N :=
  Units.map e.mapMatrix.toMonoidHom D

theorem phaseWeylUnit_map : mapPhaseMatrixUnit N e (phaseWeylUnit F N) = phaseWeylUnit k N := by
  apply Units.ext
  ext i j
  cases i <;> cases j <;>
    simp [mapPhaseMatrixUnit, phaseWeylUnit, Weil.Local.Generators.Construction.weylSymplectic_matrix,
      Matrix.fromBlocks, Matrix.one_apply]

theorem phaseUnitCoordinates_map (D : PhaseMatrixUnit F N) :
    Units.map e.mapMatrix.toMonoidHom (phaseUnitCoordinates F N D) =
      phaseUnitCoordinates k N (mapPhaseMatrixUnit N e D) := by
  apply Units.ext
  rfl

theorem cayleyCoefficientLinear_map (D : PhaseMatrixUnit F N) :
    Units.map e.mapMatrix.toMonoidHom (cayleyCoefficientLinear F N D) =
      cayleyCoefficientLinear k N (mapPhaseMatrixUnit N e D) := by
  unfold cayleyCoefficientLinear
  rw [map_inv, phaseUnitCoordinates_map]
  have hm : mapPhaseMatrixUnit N e (phaseWeylUnit F N * D⁻¹) =
      phaseWeylUnit k N * (mapPhaseMatrixUnit N e D)⁻¹ := by
    change Units.map e.mapMatrix.toMonoidHom (phaseWeylUnit F N * D⁻¹) = _
    rw [map_mul, map_inv]
    rw [show Units.map e.mapMatrix.toMonoidHom (phaseWeylUnit F N) = phaseWeylUnit k N from phaseWeylUnit_map N e]
    rfl
  rw [hm]

variable [CharZero F] [CharZero k]

theorem cayleyCoefficientQuadratic_map (D : PhaseMatrixUnit F N) :
    (cayleyCoefficientQuadratic F N D).val.map e =
      (cayleyCoefficientQuadratic k N (mapPhaseMatrixUnit N e D)).val := by
  unfold cayleyCoefficientQuadratic
  rw [QuadraticMatrixCoordinates.Construction.symmetricPart_map]
  congr 2
  have hdi : (mapPhaseMatrixUnit N e D)⁻¹.val = D⁻¹.val.map e := by
    change (Units.map e.mapMatrix.toMonoidHom D)⁻¹.val = _
    rw [← map_inv]
    rfl
  rw [hdi]
  have hm : (D⁻¹.valᵀ * Matrix.J (Fin N) F).map e =
      (D⁻¹.val.map e)ᵀ * Matrix.J (Fin N) k := by
    rw [Matrix.map_mul, Matrix.map_J]
    rfl
  exact congrArg (Matrix.reindex finSumFinEquiv finSumFinEquiv) hm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyMatrixBaseChange.Construction
