import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactPlaneElimination

/-! # Compact Plane Perfect -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactPlanePerfect.CM

noncomputable section

/-! Hermitian diagonalization proves perfectness of the actual compact
two-dimensional special-unitary group. -/

open scoped ComplexConjugate
open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

def compactPlaneHermitian (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a.im : ℂ), -Complex.I * b; Complex.I * conj b, -(a.im : ℂ)]

theorem compact_plane_hermitian (a b : ℂ) : (compactPlaneHermitian a b).IsHermitian := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [compactPlaneHermitian]

theorem compact_plane_hermitian_reconstruct (a b : ℂ) :
    CompactPlaneElimination.CM.compactPlaneMatrix a b = (a.re : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Complex.I • compactPlaneHermitian a b := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [CompactPlaneElimination.CM.compactPlaneMatrix, compactPlaneHermitian, Complex.mul_re, Complex.mul_im]

theorem compact_plane_diagonalize (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    ∃ (u : Matrix.unitaryGroup (Fin 2) ℂ) (d : Fin 2 → ℂ),
      g.val.val = _root_.Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) u
        (Matrix.diagonal d) := by
  let a := g.val.val 0 0
  let b := g.val.val 0 1
  have hg : g.val.val = CompactPlaneElimination.CM.compactPlaneMatrix a b := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact (CompactPlaneElimination.CM.compact_plane_shape g).1
    · exact (CompactPlaneElimination.CM.compact_plane_shape g).2
  let hH := compact_plane_hermitian a b
  let u := hH.eigenvectorUnitary
  let d := fun i => (a.re : ℂ) + Complex.I * (hH.eigenvalues i : ℂ)
  refine ⟨u, d, ?_⟩
  have hd : Matrix.diagonal d = (a.re : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Complex.I • Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j; simp [d]
    · simp [Matrix.diagonal, hij]
  rw [hd, map_add, map_smul, map_one, map_smul]
  have hspec : compactPlaneHermitian a b =
      _root_.Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) u
        (Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))) := hH.spectral_theorem
  rw [← hspec, hg, compact_plane_hermitian_reconstruct]

theorem compact_plane_commutator_eq_top :
    commutator (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨u, d, hdiag⟩ := compact_plane_diagonalize g
  let h := SplitUnitaryPlane.CM.conjugateSpecialUnitary 1 (SplitUnitaryPlane.CM.compactUnitaryMatrix u⁻¹) g
  have hM : h.val.val = Matrix.diagonal d := by
    change _root_.Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) u⁻¹ g.val.val = _
    rw [hdiag, ← StarAlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have h01 : h.val.val 0 1 = 0 := by rw [hM]; simp
  have hzsq : Complex.normSq (h.val.val 0 0) = 1 := by
    have hn := CompactPlaneElimination.CM.compact_plane_norm h
    simpa only [h01, Complex.normSq_zero, add_zero] using hn
  let z : Circle := ⟨h.val.val 0 0, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [Complex.normSq_eq_norm_sq] at hzsq
    nlinarith [norm_nonneg (h.val.val 0 0)]⟩
  have hz : h = CompactPlaneElimination.CM.compactPlaneDiagonal z := by
    apply Subtype.ext
    apply Units.ext
    change h.val.val = CompactPlaneElimination.CM.compactPlaneMatrix z 0
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact h01
    · simpa [CompactPlaneElimination.CM.compactPlaneMatrix, h01] using (CompactPlaneElimination.CM.compact_plane_shape h).1
    · exact (CompactPlaneElimination.CM.compact_plane_shape h).2
  have hh : h ∈ commutator (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [hz]
    exact CompactPlaneElimination.CM.compact_plane_diagonal_mem_commutator z
  have hc := SplitUnitaryPlane.CM.hom_maps_commutator (SplitUnitaryPlane.CM.conjugateSpecialUnitary 1 (SplitUnitaryPlane.CM.compactUnitaryMatrix u)) hh
  rw [SplitUnitaryPlane.CM.compact_conjugate_cancel] at hc
  exact hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactPlanePerfect.CM
