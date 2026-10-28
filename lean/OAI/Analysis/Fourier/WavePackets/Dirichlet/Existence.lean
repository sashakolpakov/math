import OAI.Analysis.Fourier.WavePackets.Dirichlet.C4
import OAI.Analysis.PDE.Dirichlet.Rough.Moore.SmoothUpgrade
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Descent

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped ContDiff ComplexOrder

/-- The periodic quaternionic Dirichlet problem has a genuine smooth
solution for every admissible set of data. The continuity method and
the all-orders boundary regularity theorem are applied internally. -/
theorem PeriodicQuaternionicData.nonempty_solution
    {m : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] [Fintype ι]
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b) :
    Nonempty (PeriodicQuaternionicSolution D) := by
  let : FiniteDimensional ℝ P := b.finiteDimensional_of_finite
  let : FiniteDimensional ℝ V := finiteDimensional_transverse_of_split e
  let : Nontrivial (OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4) := by
    obtain ⟨v,w,hvw⟩ := exists_pair_ne V
    exact ⟨⟨e.symm (0,v),e.symm (0,w),fun h =>
      hvw (congrArg Prod.snd (e.symm.injective h))⟩⟩
  obtain ⟨ψ,hψ,hψp,hψbd,hψpos,hψeq⟩ := D.exists_C4_potential
  obtain ⟨g,hg,hgp,hgv,_hgD,hgDD⟩ :=
    OAI.Analysis.PDE.Dirichlet.exists_smooth_periodic_moore_representative D.dimension e b D.compact
      D.defining_smooth D.defining_periodic D.bounded D.regular D.defining_positive
      D.background D.density ψ D.background_smooth D.density_smooth
      (hψ.of_le (by norm_num)) D.background_periodic D.density_periodic
      hψp hψbd hψpos hψeq
  have hH (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4) (hx : D.defining x ≤ 0) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x = OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x := by
    unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
    rw [hgDD x hx]
  refine ⟨D.solutionOfPotential g hg hgp ?_ ?_ ?_⟩
  · intro x hx
    exact (hgv x hx.le).trans (hψbd x hx)
  · intro x hx
    rw [hH x hx]
    exact hψpos x hx
  · intro x hx
    rw [hH x hx]
    exact hψeq x hx

/-- The actual, unconditional four-slot existence theorem used by the
packet construction. -/
theorem fourSlotDirichletExistence : FourSlotDirichletExistence := by
  intro m P V ι _ _ _ _ _ _ e b D
  exact D.nonempty_solution

/-- Descending the checked four-slot solution gives the three-slot
periodic Dirichlet theorem of the manuscript. -/
theorem threeSlotDirichletExistence
    {m : ℕ} {P V ι : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] [Fintype ι]
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b) :
    Nonempty (PeriodicQuaternionicSolution D) :=
  threeSlotDirichlet_of_fourSlot fourSlotDirichletExistence D

end OAI.Analysis.Fourier.WavePackets
