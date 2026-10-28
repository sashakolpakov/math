import OAI.Analysis.PDE.Dirichlet.Rough.GeometricCurves
import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Periodic

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The actual domain deformation supplies all smooth periodic Hölder
coefficient curves used by the transformed Moore operator. -/
theorem PeriodicDomainDeformation.nonempty_fields
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r : E → ℝ}
    (D : PeriodicDomainDeformation e b r) {K : Set V} (hK : IsCompact K)
    (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (B f : E → ℝ) (hB : ContDiff ℝ ∞ B) (hf : ContDiff ℝ ∞ f)
    (hBp : LatticePeriodic e b (fderiv ℝ (fderiv ℝ B))) (hfp : LatticePeriodic e b f) :
    Nonempty (OAI.Analysis.PDE.Schauder.PeriodicDeformationFields r α {t | |t| < D.radius} D.map B f e b) := by
  have hI : IsOpen {t : ℝ | |t| < D.radius} := isOpen_lt continuous_abs continuous_const
  obtain ⟨C⟩ := OAI.Analysis.PDE.Schauder.nonempty_deformationFields e b hK hr hrp hbounded hα hα1 hI
    D.map D.smooth D.inverse_smooth D.bijective (fun t ht l x ↦ D.equivariant t l x)
    B f hB hf hBp hfp
  exact ⟨C.toPeriodic e b hrp D.bijective (fun t ht l x ↦ D.equivariant t l x) hBp hfp⟩

end OAI.Analysis.PDE.Dirichlet
