import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelGeometricPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.UnramifiedFieldCriterion

/-! # Kernel Unramified -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual finite-flat kernel of a positive specified polarization type is formally unramified over the original arbitrary base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.kernel_formallyUnramified
    {S : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i) : FormallyUnramified p.kernelScheme.hom := by
  apply Geometric.UnramifiedFieldCriterion.formallyUnramified_of_geometricFieldPullbacks p.kernelScheme.hom
  intro K _ _ s
  have := hp.kernel_geometricBaseChange_etale hδ K s
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
