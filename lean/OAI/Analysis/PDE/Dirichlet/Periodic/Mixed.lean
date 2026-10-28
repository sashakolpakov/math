import OAI.Analysis.PDE.Dirichlet.AllMixed
import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus

open Set Metric Module
open scoped Topology ComplexOrder MatrixOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Uniform mixed Hessian control on the physical boundary of a periodic
domain. The local barrier construction is performed only near a compact set
of representatives and then transported by periodicity. -/
theorem uniform_mixed_hessian_bound_lattice {n : ℕ} (hn : 1 ≤ n)
    (split : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {r B₀ F : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 3 B₀) (hF : ContDiff ℝ 1 F)
    (hrper : LatticePeriodic split lat r)
    (hbounded : ∀ x, r x ≤ 0 → (split x).2 ∈ C)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {b B G κ r₀ : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) (hG : 0 ≤ G) (hκ : 0 < κ) (hr₀ : 0 < r₀)
    (hconvex : ∀ x ∈ interior {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) Q))).PosSemidef) :
    ∃ M : ℝ, 0 < M ∧ ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 3 u →
      LatticePeriodic split lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x) →
      (∀ x, r x ≤ 0 → ‖fderiv ℝ u x‖ ≤ G) →
      (∀ x ∈ interior {x | r x ≤ 0},
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x ∈ interior {x | r x ≤ 0},
        κ ≤ OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) 1) →
      (∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x = 0 → ∀ v, fderiv ℝ r x v = 0 →
        |fderiv ℝ (fderiv ℝ u) x (covectorNormal (fderiv ℝ r x)) v| ≤ M * ‖v‖ := by
  let K := latticeSublevelCell split lat C r
  let S := K ∩ {x | r x = 0}
  have hK : IsCompact K := isCompact_latticeSublevelCell split lat hC hr.continuous
  have hS : IsCompact S := hK.inter_right (isClosed_eq hr.continuous continuous_const)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace (closedBall (0 : CoordinateSpace n 4) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let T := S × closedBall (0 : CoordinateSpace n 4) 1
  let z : T → CoordinateSpace n 4 := fun p ↦ p.1.1
  let e : T → CoordinateSpace n 4 := fun p ↦ p.2.1
  have hz : Continuous z := continuous_subtype_val.comp continuous_fst
  have he : Continuous e := continuous_subtype_val.comp continuous_snd
  have hcenter : ∀ p, r (z p) = 0 := fun p ↦ p.1.2.2
  obtain ⟨M, hM, hbound⟩ := compact_family_mixed_hessian_bound hn hr hB₀ hF hreg
    hz he hcenter hb hbB hG hκ hr₀ hconvex
  refine ⟨M, hM, ?_⟩
  intro u hu huper huz hub hug hup hutr hueq x hx
  let y := latticeRepresentative split lat x
  have hy : y ∈ S := ⟨latticeRepresentative_mem_sublevelCell split lat hrper hbounded hx.le,
    by change r (latticeRepresentative split lat x) = 0; rw [hrper.representative, hx]⟩
  have hDr : fderiv ℝ r y = fderiv ℝ r x := hrper.fderiv.representative x
  have hD2u : fderiv ℝ (fderiv ℝ u) y = fderiv ℝ (fderiv ℝ u) x :=
    huper.fderiv.fderiv.representative x
  apply linear_bound_on_kernel_of_unit_ball (fderiv ℝ (fderiv ℝ u) x (covectorNormal (fderiv ℝ r x)))
    (fderiv ℝ r x)
  intro v hv hnv
  have hv' : v ∈ closedBall (0 : CoordinateSpace n 4) 1 := by simpa using hnv
  have h := hbound u hu huz hub hug hup hutr hueq (⟨y, hy⟩, ⟨v, hv'⟩)
  change fderiv ℝ r y v = 0 →
    |fderiv ℝ (fderiv ℝ u) y (covectorNormal (fderiv ℝ r y)) v| ≤ M at h
  rw [hDr, hD2u] at h
  exact h hv

end OAI.Analysis.PDE.Dirichlet
