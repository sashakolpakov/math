import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Fields
import OAI.Analysis.PDE.Schauder.Calculus.HolderPeriodicity

open Set Module
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

structure PeriodicDeformationFields (r : E → ℝ) (α : ℝ) (I : Set ℝ)
    (Φ : ℝ × E → E) (B₀ f : E → ℝ) (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) where
  fields : DeformationFields r α I Φ B₀ f
  background_periodic : ∀ t ∈ I, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (fields.background t)))
  jacobian_periodic : ∀ t ∈ I, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (fields.jacobian t)))
  curvature_periodic : ∀ t ∈ I, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (fields.curvature t)))
  source_periodic : ∀ t ∈ I, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (fields.source t)))

def DeformationFields.toPeriodic
    {r : E → ℝ} {α : ℝ} {I : Set ℝ} {Φ : ℝ × E → E} {B₀ f : E → ℝ}
    (C : DeformationFields r α I Φ B₀ f)
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbij : ∀ t ∈ I, Function.Bijective (fun x => Φ (t,x)))
    (hper : ∀ t ∈ I, ∀ l : Submodule.span ℤ (Set.range b), ∀ x,
      Φ (t,x+e.symm ((l:P),0)) = Φ (t,x)+e.symm ((l:P),0))
    (hpB : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fderiv ℝ (fderiv ℝ B₀))) (hpf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) :
    PeriodicDeformationFields r α I Φ B₀ f e b where
  fields := C
  background_periodic t ht := holder_periodic_of_actual e b hr (C.background t)
    (fun x => fderiv ℝ (fderiv ℝ B₀) (Φ (t,x)))
    (latticePeriodic_comp_equivariant e b hpB _ (hper t ht)) (C.background_value t ht)
  jacobian_periodic t ht := by
    apply holder_periodic_of_actual e b hr (C.jacobian t) (fun x => OAI.Analysis.PDE.Dirichlet.inverseJacobian Φ (t,x))
    · intro x l
      rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq,add_comm (e.symm ((l:P),0)) x]
      exact OAI.Analysis.PDE.Dirichlet.inverseJacobian_periodic t (hbij t ht) _ (hper t ht l) x
    · exact C.jacobian_value t ht
  curvature_periodic t ht := by
    apply holder_periodic_of_actual e b hr (C.curvature t) (fun x => OAI.Analysis.PDE.Dirichlet.inverseHessian Φ (t,x))
    · intro x l
      rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq,add_comm (e.symm ((l:P),0)) x]
      exact OAI.Analysis.PDE.Dirichlet.inverseHessian_periodic t (hbij t ht) _ (hper t ht l) x
    · exact C.curvature_value t ht
  source_periodic t ht := holder_periodic_of_actual e b hr (C.source t)
    (fun x => f (Φ (t,x))) (latticePeriodic_comp_equivariant e b hpf _ (hper t ht))
    (C.source_value t ht)

end OAI.Analysis.PDE.Schauder
