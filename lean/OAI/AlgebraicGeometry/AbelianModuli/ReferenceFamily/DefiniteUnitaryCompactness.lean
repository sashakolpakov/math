import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveHermitianCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm
import OAI.RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology
import OAI.RepresentationTheory.Theta.Adelic.CompactStandardUnitary

/-! # Definite Unitary Compactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DefiniteUnitaryCompactness

noncomputable section

/-! A definite Hermitian form has compact special unitary group. The
orthonormal coordinates are constructed from the actual form, and the
result transports through any specified continuous complex coordinate
on a native archimedean coefficient field. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology OAI.RepresentationTheory.Theta.Adelic.CompactStandardUnitary

theorem formValue_linearFirst (H : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue H x y = ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm H.transpose y x := by
  simp only [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec, dotProduct, ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply,
    Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem complex_specialUnitary_compact_of_positive
    (H : Matrix (Fin 3) (Fin 3) ℂ) (hH : H.conjTranspose = H)
    (hpos : ∀ x : Fin 3 → ℂ, x ≠ 0 → 0 < (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue H x x).re) :
    CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H) := by
  let F := ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm H.transpose
  have hsym (x y : Fin 3 → ℂ) : F y x = star (F x y) := by
    apply ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_symmetry
    intro i j
    exact (congrArg (fun M => M j i) hH).symm
  have hFpos (x : Fin 3 → ℂ) (hx : x ≠ 0) : 0 < (F x x).re := by
    rw [← formValue_linearFirst]
    exact hpos x hx
  obtain ⟨e, he⟩ := PositiveHermitianCoordinates.exists_positiveHermitian_coordinates F hsym hFpos 3 (by simp)
  let B : (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e.symm)
  have hBv (x : Fin 3 → ℂ) : B.val.mulVec x = e.symm x := by
    exact LinearMap.congr_fun (Matrix.toLin'_toMatrix' e.symm.toLinearMap) x
  have hform (x y : Fin 3 → ℂ) :
      RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue H (B.val.mulVec x) (B.val.mulVec y) = RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue 1 x y := by
    rw [hBv, hBv, formValue_linearFirst]
    change F (e.symm y) (e.symm x) = _
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
    simp only [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.one_mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hB : B.val.conjTranspose * H * B.val = 1 := by
    ext i j
    have h := hform (Pi.single i 1) (Pi.single j 1)
    rw [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue_change] at h
    simpa [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite] using h
  let : CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 3) (Fin 3) ℂ)) := RepresentationTheory.Theta.Adelic.CompactStandardUnitary.standardUnitary_compact
  exact (RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology.specialUnitaryBasisContinuousEquiv H 1 B hB).symm.toHomeomorph.compactSpace

theorem specialUnitary_neg (H : Matrix (Fin 3) (Fin 3) ℂ) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.specialUnitary (-H) = RepresentationTheory.Theta.Adelic.SpecialUnitary.specialUnitary H := by
  ext g
  change (g.val.conjTranspose * (-H) * g.val = -H ∧
      Matrix.GeneralLinearGroup.det g = 1) ↔
    (g.val.conjTranspose * H * g.val = H ∧ Matrix.GeneralLinearGroup.det g = 1)
  rw [mul_neg, neg_mul, neg_inj]

theorem complex_specialUnitary_compact_of_definite
    (H : Matrix (Fin 3) (Fin 3) ℂ) (hH : H.conjTranspose = H)
    (hdef : (∀ x : Fin 3 → ℂ, x ≠ 0 → 0 < (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 → (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue H x x).re < 0)) :
    CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H) := by
  rcases hdef with hpos | hneg
  · exact complex_specialUnitary_compact_of_positive H hH hpos
  · have hHneg : (-H).conjTranspose = -H := by
      rw [Matrix.conjTranspose_neg, hH]
    have hpos (x : Fin 3 → ℂ) (hx : x ≠ 0) : 0 < (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (-H) x x).re := by
      have hform : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (-H) x x = -RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue H x x := by
        simp [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec, dotProduct]
      rw [hform, Complex.neg_re]
      exact neg_pos.mpr (hneg x hx)
    let : CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (-H)) :=
      complex_specialUnitary_compact_of_positive (-H) hHneg hpos
    have he : (RepresentationTheory.Theta.Adelic.SpecialUnitary.specialUnitary (-H) : Set (Matrix (Fin 3) (Fin 3) ℂ)ˣ) =
        (RepresentationTheory.Theta.Adelic.SpecialUnitary.specialUnitary H : Set (Matrix (Fin 3) (Fin 3) ℂ)ˣ) :=
      congrArg SetLike.coe (specialUnitary_neg H)
    exact (Homeomorph.setCongr he).compactSpace

theorem field_specialUnitary_compact_of_definite
    {R : Type*} [CommRing R] [StarRing R] [TopologicalSpace R]
    (e : R ≃+* ℂ) (hs : ∀ x, e (star x) = star (e x))
    (hc : Continuous e) (hi : Continuous e.symm)
    (H : Matrix (Fin 3) (Fin 3) R) (hH : H.conjTranspose = H)
    (hdef : (∀ x : Fin 3 → ℂ, x ≠ 0 → 0 < (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (H.map e.toRingHom) x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 → (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (H.map e.toRingHom) x x).re < 0)) :
    CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H) := by
  have heH : (H.map e.toRingHom).conjTranspose = H.map e.toRingHom := by
    ext i j
    change star (e (H j i)) = e (H i j)
    rw [← hs]
    exact congrArg e (congrArg (fun M => M i j) hH)
  let : CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map e.toRingHom)) :=
    complex_specialUnitary_compact_of_definite (H.map e.toRingHom) heH hdef
  exact (RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology.specialUnitaryFieldContinuousEquiv e hs hc hi H).symm.toHomeomorph.compactSpace

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DefiniteUnitaryCompactness
