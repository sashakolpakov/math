import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Split Unitary Plane -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitUnitaryPlane.CM

noncomputable section

section

/-! The actual two-dimensional split special-unitary group is an image
of SL(2,R). Its characters vanish by the elementary-matrix commutator
theorem, without a supplied Lie-group realization. -/

open scoped ComplexConjugate
open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

def splitPlaneForm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def splitPlaneMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((A 0 0 + A 1 1 : ℝ) : ℂ) / 2 + Complex.I * ((A 1 0 - A 0 1 : ℝ) : ℂ) / 2,
      ((A 0 0 - A 1 1 : ℝ) : ℂ) / 2 + Complex.I * ((A 1 0 + A 0 1 : ℝ) : ℂ) / 2;
     ((A 0 0 - A 1 1 : ℝ) : ℂ) / 2 - Complex.I * ((A 1 0 + A 0 1 : ℝ) : ℂ) / 2,
      ((A 0 0 + A 1 1 : ℝ) : ℂ) / 2 - Complex.I * ((A 1 0 - A 0 1 : ℝ) : ℂ) / 2]

theorem split_plane_matrix_det (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (splitPlaneMatrix A).det = (A.det : ℂ) := by
  apply Complex.ext <;>
    simp [splitPlaneMatrix, Matrix.det_fin_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem split_plane_matrix_form (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (splitPlaneMatrix A).conjTranspose * splitPlaneForm * splitPlaneMatrix A =
      (A.det : ℂ) • splitPlaneForm := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [splitPlaneMatrix, splitPlaneForm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

def splitPlaneSL : Matrix.SpecialLinearGroup (Fin 2) ℝ →*
    Matrix.SpecialLinearGroup (Fin 2) ℂ where
  toFun A := ⟨splitPlaneMatrix A.val, by rw [split_plane_matrix_det, A.property, Complex.ofReal_one]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [splitPlaneMatrix]
  map_mul' A B := by
    apply Subtype.ext
    change splitPlaneMatrix (A.val * B.val) = splitPlaneMatrix A.val * splitPlaneMatrix B.val
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [splitPlaneMatrix, Matrix.mul_apply,
        Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

def splitPlaneHom : Matrix.SpecialLinearGroup (Fin 2) ℝ →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU splitPlaneForm where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL (splitPlaneSL A), by
    constructor
    · change (splitPlaneMatrix A.val).conjTranspose * splitPlaneForm * splitPlaneMatrix A.val = _
      rw [split_plane_matrix_form, A.property, Complex.ofReal_one, one_smul]
    · exact Matrix.SpecialLinearGroup.coeToGL_det (splitPlaneSL A)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by simp)

theorem split_plane_shape (A : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hA : A.val.conjTranspose * splitPlaneForm * A.val = splitPlaneForm) :
    A 1 0 = conj (A 0 1) ∧ A 1 1 = conj (A 0 0) := by
  have h : A.val.conjTranspose * splitPlaneForm = splitPlaneForm * (A⁻¹).val := by
    calc
      _ = (A.val.conjTranspose * splitPlaneForm * A.val) * (A⁻¹).val := by
        rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
      _ = _ := congrArg (fun M => M * (A⁻¹).val) hA
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp [splitPlaneForm, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  exact ⟨by simpa using congrArg conj h01, h00.symm⟩

def splitPlaneRealMatrix (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(A 0 0).re + (A 0 1).re, (A 0 1).im - (A 0 0).im;
     (A 0 0).im + (A 0 1).im, (A 0 0).re - (A 0 1).re]

theorem split_plane_real_inverse (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h10 : A 1 0 = conj (A 0 1)) (h11 : A 1 1 = conj (A 0 0)) :
    splitPlaneMatrix (splitPlaneRealMatrix A) = A := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [splitPlaneMatrix, splitPlaneRealMatrix, h10, h11,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem split_plane_hom_surjective : Function.Surjective splitPlaneHom := by
  intro g
  let A : Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨g.val.val, congrArg Units.val g.property.2⟩
  have hshape := split_plane_shape A g.property.1
  have hback := split_plane_real_inverse A.val hshape.1 hshape.2
  have hdet : (splitPlaneRealMatrix A.val).det = 1 := by
    apply Complex.ofReal_injective
    rw [← split_plane_matrix_det, hback, A.property, Complex.ofReal_one]
  refine ⟨⟨splitPlaneRealMatrix A.val, hdet⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hback

theorem split_plane_commutator_eq_top : commutator (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU splitPlaneForm) = ⊤ := by
  have hR : commutator (Matrix.SpecialLinearGroup (Fin 2) ℝ) = ⊤ :=
    Matrix.SL2.commutator_eq_top (a := (2 : ℝ)) (by norm_num) (by norm_num)
  apply top_unique
  intro g _
  obtain ⟨a, rfl⟩ := split_plane_hom_surjective g
  have ha : a ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) ℝ) := by rw [hR]; trivial
  have hm := Subgroup.mem_map_of_mem splitPlaneHom ha
  rw [map_commutator_eq] at hm
  exact Subgroup.commutator_mono le_top le_top hm

end

/-! Conjugation and commutator transport for the actual special-unitary
matrix subgroup. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

def conjugateSpecialUnitary {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (u : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H) : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H where
  toFun g := ⟨u.val * g.val * u.val⁻¹, by
    constructor
    · exact (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryIsometries H).mul_mem
        ((RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryIsometries H).mul_mem u.property g.property.1)
        ((RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryIsometries H).inv_mem u.property)
    · change Matrix.GeneralLinearGroup.det (u.val * g.val * u.val⁻¹) = 1
      rw [map_mul, map_mul, map_inv, g.property.2, mul_one, mul_inv_cancel]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

theorem hom_maps_commutator {G T : Type*} [Group G] [Group T] (f : G →* T)
    {g : G} (hg : g ∈ commutator G) : f g ∈ commutator T := by
  have h := Subgroup.mem_map_of_mem f hg
  rw [map_commutator_eq] at h
  exact Subgroup.commutator_mono le_top le_top h

def compactUnitaryMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (u : Matrix.unitaryGroup n ℂ) : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (1 : Matrix n n ℂ) :=
  ⟨_root_.Unitary.toUnits u, by
    change (u : Matrix n n ℂ).conjTranspose * 1 * (u : Matrix n n ℂ) = 1
    rw [Matrix.mul_one]
    exact _root_.Unitary.coe_star_mul_self u⟩

def specialUnitaryOfMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (H M : Matrix n n ℂ) (hdet : M.det = 1) (hform : M.conjTranspose * H * M = H) : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H :=
  ⟨Matrix.SpecialLinearGroup.toGL ⟨M, hdet⟩, hform,
    Matrix.SpecialLinearGroup.coeToGL_det ⟨M, hdet⟩⟩

theorem compact_conjugate_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (u : Matrix.unitaryGroup n ℂ) (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix n n ℂ)) :
    (conjugateSpecialUnitary 1 (compactUnitaryMatrix u) g).val.val =
      (u : Matrix n n ℂ) * g.val.val * (u : Matrix n n ℂ).conjTranspose := rfl

theorem compact_conjugate_cancel {n : Type*} [Fintype n] [DecidableEq n]
    (u : Matrix.unitaryGroup n ℂ) (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix n n ℂ)) :
    conjugateSpecialUnitary 1 (compactUnitaryMatrix u)
      (conjugateSpecialUnitary 1 (compactUnitaryMatrix u⁻¹) g) = g := by
  apply Subtype.ext
  apply Units.ext
  rw [compact_conjugate_matrix, compact_conjugate_matrix]
  change u.val * (u.val.conjTranspose * g.val.val *
    u.val.conjTranspose.conjTranspose) * u.val.conjTranspose = g.val.val
  rw [Matrix.conjTranspose_conjTranspose]
  have hu : u.val * u.val.conjTranspose = 1 := _root_.Unitary.coe_mul_star_self u
  simp only [← mul_assoc, hu, one_mul]
  rw [mul_assoc, hu, mul_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitUnitaryPlane.CM
