import OAI.Analysis.Fourier.WavePackets.FlowCoefficients
import OAI.Analysis.PDE.Concentration.Packet.PeriodBasis

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Dirichlet.ParameterDeformation OAI.Analysis.PDE.Concentration

variable {Z T E F P V ι : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r : E → ℝ}

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace T] [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι] in
theorem flowPullback_periodic (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    {f : Z × E → F} (hf : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (z,x))) (z : Z) (t : T) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => flowPullback D.map f ((z,t),x)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i x
  let l : Submodule.span ℤ (Set.range b) := ⟨b i,Submodule.subset_span (Set.mem_range_self i)⟩
  change f (z,D.map (t,x+e.symm ((l:P),0))) = f (z,D.map (t,x))
  rw [D.equivariant]
  exact OAI.Analysis.PDE.Dirichlet.ParameterDeformation.latticePeriodic_add_shift e b (hf z) _ l

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace T] [Fintype ι] in
theorem flowJacobian_periodic (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    {J : Z × E → E →L[ℝ] E} (hJ : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => J (z,x)))
    (z : Z) (t : T) (ht : ‖t‖ < D.radius) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => flowJacobian D.map J ((z,t),x)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i x
  let l : Submodule.span ℤ (Set.range b) := ⟨b i,Submodule.subset_span (Set.mem_range_self i)⟩
  have hA := OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian_periodic t (D.bijective t ht) (e.symm ((l:P),0))
    (D.equivariant t l) x
  have hp := OAI.Analysis.PDE.Dirichlet.ParameterDeformation.latticePeriodic_add_shift e b (flowPullback_periodic D hJ z t) x l
  change flowPullback D.map J ((z,t),x+e.symm ((l:P),0)) =
    flowPullback D.map J ((z,t),x) at hp
  change (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian D.map (t,x+e.symm ((l:P),0))).comp
    (flowPullback D.map J ((z,t),x+e.symm ((l:P),0))) = _
  rw [hA,hp]
  rfl

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace T] [Fintype ι] in
theorem flowCurvature_periodic (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    {J : Z × E → E →L[ℝ] E} (hJ : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => J (z,x)))
    {K : Z × E → E →L[ℝ] E →L[ℝ] E} (hK : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => K (z,x)))
    (z : Z) (t : T) (ht : ‖t‖ < D.radius) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => flowCurvature D.map J K ((z,t),x)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i x
  let l : Submodule.span ℤ (Set.range b) := ⟨b i,Submodule.subset_span (Set.mem_range_self i)⟩
  have hA := OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian_periodic t (D.bijective t ht) (e.symm ((l:P),0))
    (D.equivariant t l) x
  have hB := OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseHessian_periodic t (D.bijective t ht) (e.symm ((l:P),0))
    (D.equivariant t l) x
  have hj := OAI.Analysis.PDE.Dirichlet.ParameterDeformation.latticePeriodic_add_shift e b (flowPullback_periodic D hJ z t) x l
  have hk := OAI.Analysis.PDE.Dirichlet.ParameterDeformation.latticePeriodic_add_shift e b (flowPullback_periodic D hK z t) x l
  change flowPullback D.map J ((z,t),x+e.symm ((l:P),0)) =
    flowPullback D.map J ((z,t),x) at hj
  change flowPullback D.map K ((z,t),x+e.symm ((l:P),0)) =
    flowPullback D.map K ((z,t),x) at hk
  change composeInverseCurvature (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian D.map (t,x+e.symm ((l:P),0)))
    (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseHessian D.map (t,x+e.symm ((l:P),0)))
    (flowPullback D.map J ((z,t),x+e.symm ((l:P),0)))
    (flowPullback D.map K ((z,t),x+e.symm ((l:P),0))) = _
  rw [hA,hB,hj,hk]
  rfl

end OAI.Analysis.Fourier.WavePackets
