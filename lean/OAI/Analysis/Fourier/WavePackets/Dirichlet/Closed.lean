import OAI.Analysis.Fourier.WavePackets.PeriodicDirichlet
import OAI.Analysis.PDE.Dirichlet.Closed.Admissible
import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJet

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder
open scoped ContDiff ComplexOrder

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b}

/-- The equation holds on the closed fiber, by regularity of its boundary. -/
theorem PeriodicQuaternionicSolution.closed_equation (S : PeriodicQuaternionicSolution D) :
    ∀ x, D.defining x ≤ 0 →
      OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => D.background y + S.u y) x) = D.density x := by
  apply OAI.Analysis.PDE.Dirichlet.equality_on_regular_sublevel_of_interior (D.defining_smooth.of_le (by simp)) D.regular
    (OAI.Analysis.PDE.Dirichlet.continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots ((D.background_smooth.add S.smooth).of_le (by simp)))
    D.density_smooth.continuous
  intro x hx
  exact S.equation x (OAI.Analysis.PDE.Dirichlet.neg_of_mem_interior_regular_sublevel D.regular hx)

/-- Strict closed-fiber admissibility follows from the positive right hand
side, not from an extra boundary positivity assumption. -/
theorem PeriodicQuaternionicSolution.closed_positive (S : PeriodicQuaternionicSolution D) :
    ∀ x, D.defining x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => D.background y + S.u y) x)).PosDef :=
  OAI.Analysis.PDE.Dirichlet.quaternionHessian_posDef_on_regular_sublevel (D.defining_smooth.of_le (by simp)) D.regular
    ((D.background_smooth.add S.smooth).of_le (by simp)) D.density_smooth.continuous
    D.density_positive S.admissible S.equation

/-- A classical periodic solution yields its genuine closed-domain Banach
jet, including its actual first and second derivatives. -/
theorem PeriodicQuaternionicSolution.exists_banach_jet (S : PeriodicQuaternionicSolution D)
    {hΩD : {x | D.defining x < 0} ⊆ {x | D.defining x ≤ 0}}
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e b,
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value U.val x = S.u x) ∧
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U.val x = fderiv ℝ S.u x) ∧
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U.val x =
        fderiv ℝ (fderiv ℝ S.u) x) := by
  obtain ⟨U,_,_,_,hU₀,hU₁,hU₂,hU⟩ := OAI.Analysis.PDE.Dirichlet.exists_periodic_dirichlet_C2Holder_jet e b D.compact
    D.defining_smooth.continuous D.defining_periodic D.bounded S.u
    (S.smooth.of_le (by simp)) S.periodic S.boundary hα hα1
  exact ⟨⟨U,hU⟩,hU₀,hU₁,hU₂⟩

/-- Both the correction and full potential have their actual Banach jets. -/
theorem PeriodicQuaternionicSolution.exists_full_banach_jet (S : PeriodicQuaternionicSolution D)
    {hΩD : {x | D.defining x < 0} ⊆ {x | D.defining x ≤ 0}}
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e b,
      ∃ g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α,
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value U.val x = S.u x) ∧
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U.val x = fderiv ℝ S.u x) ∧
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U.val x =
        fderiv ℝ (fderiv ℝ S.u) x) ∧
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x =
        fderiv ℝ (fderiv ℝ (fun y => D.background y + S.u y)) x) ∧
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value g x = D.background x + S.u x) ∧
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)) := by
  obtain ⟨U,hU₀,hU₁,hU₂⟩ := S.exists_banach_jet (hΩD := hΩD) hα hα1
  obtain ⟨g,_,_,_,hg₀,_,hg₂,hgp⟩ := OAI.Analysis.PDE.Dirichlet.exists_periodic_C2Holder_jet e b D.compact
    D.defining_smooth.continuous D.defining_periodic D.bounded (hΩD := hΩD)
    (fun y => D.background y + S.u y)
    ((D.background_smooth.add S.smooth).of_le (by simp))
    (D.background_periodic.add S.periodic) hα hα1
  exact ⟨U,g,hU₀,hU₁,hU₂,hg₂,hg₀,hgp⟩

end OAI.Analysis.Fourier.WavePackets
