import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Hom
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.EndomorphismEquationPackage

/-! # Endomorphism Equation Loci -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismEquationLoci.Core

noncomputable section

/-! Full Presentations endomorphism equation loci under the stated natural
hypotheses, for every finite system of actual morphism equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem endomorphism_equation_loci
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    (A : Over S) (BA : Has.Core.ProjectivePresentation A) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) (P : Fin n → Polynomial ℚ) (R : Endomorphisms.Core.FiniteEndomorphismEquations A n) :
    ∃ (B : Has.Core.ProjectivePresentation (A ⨯ A)) (L : Loci.Core.HilbertHomLoci A A B n P),
      Segre.Open.Core.IsSegrePresentation BA BA B ∧ Nonempty (Loci.Core.EndomorphismEquationLoci A B n P L R) := by
  obtain ⟨B, hB, ⟨L⟩⟩ := Relative.Hom.Core.relative_hilbert_and_hom_loci A A BA BA n P
  exact ⟨B, L, hB, Proper.EndomorphismEquationPackage.Core.endomorphismEquationLoci_of_proper_sources A BA L R⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismEquationLoci.Core
