import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiCohomologyFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SerreCechVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorCoherence

/-! # Zariski Serre Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiSerreVanishing.ZariskiCohomology

noncomputable section

/-! A single sufficiently positive twist kills genuine Zariski cohomology in every positive degree for every coherent sheaf on a projective coordinate quotient over a Noetherian ring. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem projective_zariski_Serre_vanishing {R : Type u} [CommRing R] [IsNoetherianRing R]
    {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ q : ℕ,
      IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (q + 1)).obj
          (Tensor.ProductSheaf.tensorModule M (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf)) := by
  obtain ⟨B, hB⟩ :=
    @SerreCechVanishing.projectiveCoherentTensorCech_eventually_vanish R _ _ n I M
      ‹M.IsQuasicoherent› ‹M.IsFiniteType›
  refine ⟨B, fun d hd q ↦ ?_⟩
  have : (Tensor.ProductSheaf.tensorModule M (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).IsQuasicoherent :=
    LineBundle.TensorCoherence.tensorModuleRight_lineBundle_quasicoherent M (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d)
  exact (hB d hd q).of_iso
    (CechZariskiComparison.projectiveCechZariskiModuleIso I (Tensor.ProductSheaf.tensorModule M (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf) q).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiSerreVanishing.ZariskiCohomology
