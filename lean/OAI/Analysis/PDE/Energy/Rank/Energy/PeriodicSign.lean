import OAI.Analysis.PDE.Energy.Rank.Energy.Sign
import OAI.Analysis.PDE.Dirichlet.Periodic.Comparison

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Set Filter Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology MatrixOrder ComplexOrder

theorem correction_nonpos_singular_representatives {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {B u r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    {K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hK : IsCompact K) (hKD : K ⊆ {x | r x ≤ 0}) (hr : Continuous r)
    (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (hrep : ∀ x, r x ≤ 0 → p x ∈ K)
    (hup : ∀ x, r x ≤ 0 → u (p x) = u x)
    (hpos : ∀ x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosDef)
    (hsing : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0)
    (hbd : ∀ x, r x = 0 → u x = 0) : ∀ x, r x ≤ 0 → u x ≤ 0 := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨p x, hrep x hx⟩ hu.continuous.continuousOn
  by_cases hyz : r y = 0
  · rw [← hup x hx]
    exact (hmax (hrep x hx)).trans_eq (hbd y hyz)
  · have hyneg : r y < 0 := lt_of_le_of_ne (hKD hy) hyz
    have hm := OAI.Analysis.PDE.Dirichlet.localMax_of_compact_representatives p hr hrep hup hyneg hmax
    exact False.elim (not_localMax_of_singular_background e hB hu (hpos y hyneg) (hsing y hyneg) hm)

theorem correction_nonpos_singular_lattice {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {n s : ℕ} (slots : Fin s → Quaternion ℝ)
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {B u r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u) (hr : Continuous r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u)
    (hpos : ∀ x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => B y + u y) x)).PosDef)
    (hsing : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots B x) = 0)
    (hbd : ∀ x, r x = 0 → u x = 0) : ∀ x, r x ≤ 0 → u x ≤ 0 := by
  exact correction_nonpos_singular_representatives slots (OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b)
    (OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hC hr) inter_subset_right hr hB hu
    (fun x hx => OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e b hrper hbounded hx)
    (fun x _ => huper.representative x) hpos hsing hbd

end OAI.Analysis.PDE.Energy
