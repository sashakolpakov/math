import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitUnitaryPlane

/-! # Compact Plane Elimination -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactPlaneElimination.CM

noncomputable section

section

/-! Explicit compact two-dimensional special-unitary matrices and the
commutators representing their diagonal circle. -/

open scoped ComplexConjugate commutatorElement
open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

def compactPlaneMatrix (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a, b; -conj b, conj a]

theorem compact_plane_det (a b : ℂ) :
    (compactPlaneMatrix a b).det = ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) := by
  simp [compactPlaneMatrix, Matrix.det_fin_two, Complex.mul_conj, Complex.ofReal_add]

theorem compact_plane_form (a b : ℂ) :
    (compactPlaneMatrix a b).conjTranspose * 1 * compactPlaneMatrix a b =
      ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [compactPlaneMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_conj, mul_comm, add_comm]

def compactPlaneElement (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  SplitUnitaryPlane.CM.specialUnitaryOfMatrix 1 (compactPlaneMatrix a b)
    (by rw [compact_plane_det, h, Complex.ofReal_one])
    (by rw [compact_plane_form, h, Complex.ofReal_one, one_smul])

def compactPlaneDiagonal (z : Circle) : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  compactPlaneElement z 0 (by simp)

def compactPlaneWeyl : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  compactPlaneElement 0 1 (by simp)

theorem compact_plane_element_inverse (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) :
    (compactPlaneElement a b h)⁻¹.val.val = !![conj a, -b; conj b, a] := by
  change Matrix.adjugate (compactPlaneMatrix a b) = _
  rw [Matrix.adjugate_fin_two]
  simp [compactPlaneMatrix]

theorem compact_plane_diagonal_commutator (z : Circle) :
    ⁅compactPlaneDiagonal z, compactPlaneWeyl⁆ = compactPlaneDiagonal (z ^ 2) := by
  apply Subtype.ext
  apply Units.ext
  rw [commutatorElement_def]
  change (compactPlaneDiagonal z).val.val * compactPlaneWeyl.val.val *
    (compactPlaneDiagonal z)⁻¹.val.val * compactPlaneWeyl⁻¹.val.val = _
  rw [compactPlaneDiagonal, compactPlaneWeyl, compact_plane_element_inverse,
    compact_plane_element_inverse]
  change compactPlaneMatrix z 0 * compactPlaneMatrix 0 1 *
    !![conj (z : ℂ), -0; conj 0, z] * !![conj 0, -1; conj 1, 0] = compactPlaneMatrix (z ^ 2) 0
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [compactPlaneMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two]

theorem compact_plane_diagonal_mem_commutator (z : Circle) :
    compactPlaneDiagonal z ∈ commutator (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  let w := Circle.exp (Complex.arg z / 2)
  have hw : w ^ 2 = z := by
    dsimp [w]
    rw [pow_two, ← Circle.exp_add, add_halves, Circle.exp_arg]
  rw [← hw, ← compact_plane_diagonal_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem compact_plane_shape (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    g.val.val 1 0 = -conj (g.val.val 0 1) ∧ g.val.val 1 1 = conj (g.val.val 0 0) := by
  let A : Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨g.val.val, congrArg Units.val g.property.2⟩
  have hA : A.val.conjTranspose * A.val = 1 := by
    have hp : g.val.val.conjTranspose * 1 * g.val.val = 1 := g.property.1
    simpa only [Matrix.mul_one] using hp
  have h : A.val.conjTranspose = (A⁻¹).val := by
    calc
      _ = (A.val.conjTranspose * A.val) * (A⁻¹).val := by
        rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
      _ = _ := by rw [hA, one_mul]
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] at h00 h01
  exact ⟨by simpa using congrArg conj h01, h00.symm⟩

theorem compact_plane_norm (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    Complex.normSq (g.val.val 0 0) + Complex.normSq (g.val.val 0 1) = 1 := by
  have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
  rw [Matrix.det_fin_two, (compact_plane_shape g).1, (compact_plane_shape g).2] at hd
  have hr := congrArg Complex.re hd
  simpa [Complex.mul_conj] using hr

end

/-! Explicit elimination in the actual compact unitary plane. -/

open scoped ComplexConjugate
open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

def compactPlaneEliminator (x z : ℂ) (r : ℝ) (hr : 0 < r)
    (hn : Complex.normSq z + Complex.normSq x = r ^ 2) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  compactPlaneElement (z / (r : ℂ)) (-x / (r : ℂ)) (by
    simp only [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_ofReal,
      ← add_div, hn]
    simpa only [pow_two] using div_self (pow_ne_zero 2 (ne_of_gt hr)))

theorem compact_plane_eliminator_action (x z : ℂ) (r : ℝ) (hr : 0 < r)
    (hn : Complex.normSq z + Complex.normSq x = r ^ 2) :
    (compactPlaneEliminator x z r hr hn).val.val.mulVec ![x, z] = ![0, (r : ℂ)] := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hc : z * conj z + x * conj x = (r : ℂ) ^ 2 := by
    simpa only [Complex.mul_conj, Complex.ofReal_add, Complex.ofReal_pow] using congrArg Complex.ofReal hn
  change (!![z / (r : ℂ), -x / (r : ℂ);
    -conj (-x / (r : ℂ)), conj (z / (r : ℂ))] : Matrix (Fin 2) (Fin 2) ℂ).mulVec ![x, z] = _
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change z / (r : ℂ) * x + (-x / (r : ℂ)) * z = 0
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change -conj (-x / (r : ℂ)) * x + conj (z / (r : ℂ)) * z = r
    simp only [map_div₀, map_neg, Complex.conj_ofReal]
    field_simp
    linear_combination hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactPlaneElimination.CM
