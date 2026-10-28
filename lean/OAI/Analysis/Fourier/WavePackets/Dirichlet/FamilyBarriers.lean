import OAI.Analysis.Fourier.WavePackets.Dirichlet.Barriers

noncomputable section
open Set Module
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

private theorem solution_barriers_of_determinant_bounds
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b) {c B : ℝ}
    (hc : 0 < c) (hcB : c ≤ B)
    (hsmall : ∀ x, D.defining x ≤ 0 →
      OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots D.background x +
        c • OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots D.defining x) ≤ D.density x)
    (hlarge : ∀ x, D.defining x ≤ 0 → D.density x ≤
      OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots D.background x +
        B • OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots D.defining x))
    (S : PeriodicQuaternionicSolution D) :
    ∀ x, D.defining x ≤ 0 → B*D.defining x ≤ S.u x ∧ S.u x ≤ c*D.defining x := by
  have hB₀ : ContDiff ℝ 2 D.background := D.background_smooth.of_le (by simp)
  have hr : ContDiff ℝ 2 D.defining := D.defining_smooth.of_le (by simp)
  have hu : ContDiff ℝ 2 S.u := S.smooth.of_le (by simp)
  have hlower : ∀ x, D.defining x ≤ 0 →
      D.background x+B • D.defining x ≤ D.background x+S.u x := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_comparison_lattice D.dimension e b D.compact
      (hB₀.add (hr.const_smul B)) (hB₀.add hu) hr D.bounded D.defining_periodic
      (D.background_periodic.add (D.defining_periodic.smul B))
      (D.background_periodic.add S.periodic) (fun x hx => D.defining_positive x hx.le)
    · intro x hx
      rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact OAI.Analysis.PDE.Dirichlet.moore_barrier_matrix_posDef _ _ (D.background_nonnegative x hx.le)
        (D.defining_positive x hx.le) (hc.trans_le hcB)
    · intro x hx
      rw [S.equation x hx, OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact hlarge x hx.le
    · intro x hx
      simp [hx,S.boundary x hx]
  have hupper : ∀ x, D.defining x ≤ 0 →
      D.background x+S.u x ≤ D.background x+c • D.defining x := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_comparison_lattice D.dimension e b D.compact
      (hB₀.add hu) (hB₀.add (hr.const_smul c)) hr D.bounded D.defining_periodic
      (D.background_periodic.add S.periodic)
      (D.background_periodic.add (D.defining_periodic.smul c))
      (fun x hx => D.defining_positive x hx.le) S.admissible
    · intro x hx
      rw [S.equation x hx, OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact hsmall x hx.le
    · intro x hx
      simp [hx,S.boundary x hx]
  intro x hx
  exact ⟨by simpa only [smul_eq_mul,add_le_add_iff_left] using hlower x hx,
    by simpa only [smul_eq_mul,add_le_add_iff_left] using hupper x hx⟩

/-- A single pair of source barriers works for a compact family of closed
fiber representatives. Only continuity on the actual compact family is
required; no global continuity or a priori barrier constant is assumed. -/
theorem uniform_periodic_dirichlet_family_barriers
    {Z : Type*} [TopologicalSpace Z] (D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b)
    {U : Set Z} {C : Set (Z × E)} (hC : IsCompact C)
    (hclosed : ∀ p ∈ C, (D p.1).defining p.2 ≤ 0)
    (hcover : ∀ z ∈ U, ∀ x, (D z).defining x ≤ 0 →
      (z,OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x) ∈ C)
    (hA : ContinuousOn (fun p : Z × E =>
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.1).background p.2) C)
    (hR : ContinuousOn (fun p : Z × E =>
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.1).defining p.2) C)
    (hF : ContinuousOn (fun p : Z × E => (D p.1).density p.2) C) :
    ∃ B c : ℝ, 0 < c ∧ c ≤ B ∧ ∀ z ∈ U, ∀ S : PeriodicQuaternionicSolution (D z),
      ∀ x, (D z).defining x ≤ 0 →
        B*(D z).defining x ≤ S.u x ∧ S.u x ≤ c*(D z).defining x := by
  by_cases hne : C.Nonempty
  · let : CompactSpace C := isCompact_iff_compactSpace.mp hC
    let : Nonempty C := ⟨⟨hne.choose,hne.choose_spec⟩⟩
    let A : C → Matrix (Fin m) (Fin m) (Quaternion ℝ) :=
      fun p => OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.val.1).background p.val.2
    let R : C → Matrix (Fin m) (Fin m) (Quaternion ℝ) :=
      fun p => OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.val.1).defining p.val.2
    let F : C → ℝ := fun p => (D p.val.1).density p.val.2
    have hAc : Continuous A := continuousOn_iff_continuous_domRestrict.mp hA
    have hRc : Continuous R := continuousOn_iff_continuous_domRestrict.mp hR
    have hFc : Continuous F := continuousOn_iff_continuous_domRestrict.mp hF
    obtain ⟨c,B,hc,hcB,hbounds⟩ := OAI.Analysis.PDE.Dirichlet.exists_uniform_moore_barriers (D hne.choose.1).dimension
      (isCompact_univ : IsCompact (univ : Set C)) Set.univ_nonempty A R F hAc hRc hFc
      (fun p _ => (D p.val.1).background_nonnegative _ (hclosed p.val p.property))
      (fun p _ => (D p.val.1).defining_positive _ (hclosed p.val p.property))
      (fun p _ => (D p.val.1).background_degenerate _ (hclosed p.val p.property))
      (fun p _ => (D p.val.1).density_positive _ (hclosed p.val p.property))
    refine ⟨B,c,hc,hcB,fun z hz S => ?_⟩
    have hdet (x : E) (hx : (D z).defining x ≤ 0) :
        OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D z).background x +
          c • OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D z).defining x) < (D z).density x ∧
        (D z).density x < OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D z).background x +
          B • OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D z).defining x) := by
      have h := hbounds ⟨(z,OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x),hcover z hz x hx⟩ (mem_univ _)
      dsimp only [A,R,F] at h
      simpa only [((D z).background_periodic.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).representative,
        ((D z).defining_periodic.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).representative,
        (D z).density_periodic.representative] using h
    exact solution_barriers_of_determinant_bounds (D z) hc hcB
      (fun x hx => (hdet x hx).1.le) (fun x hx => (hdet x hx).2.le) S
  · refine ⟨1,1,by norm_num,le_rfl,fun z hz S x hx => ?_⟩
    exact False.elim (hne ⟨_,hcover z hz x hx⟩)

end OAI.Analysis.Fourier.WavePackets
