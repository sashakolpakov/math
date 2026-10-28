import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Loci
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Hilbert -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert

noncomputable section

/-! The two full Presentations propositions, as explicit conditional inputs.
Their types reproduce Statements/Presentations.lean at validated. No statement theorem is imported
or used as a proof of either proposition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Loci.Core

universe u

def HilbertHomInput : Prop :=
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X Y : Over S) (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (BY : HilbertScheme.Presentations.Has.Core.ProjectivePresentation Y)
    [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsSeparated Y.hom] (n : ℕ) (P : Fin n → Polynomial ℚ),
    ∃ B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ Y),
      HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BX BY B ∧ Nonempty (HilbertScheme.Presentations.Loci.Core.HilbertHomLoci X Y B n P)

def EndomorphismEquationsInput : Prop :=
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    (A : Over S) (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) (P : Fin n → Polynomial ℚ) (R : HilbertScheme.Presentations.Endomorphisms.Core.FiniteEndomorphismEquations A n),
    ∃ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A ⨯ A)) (L : HilbertScheme.Presentations.Loci.Core.HilbertHomLoci A A B n P),
      HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BA BA B ∧ Nonempty (HilbertScheme.Presentations.Loci.Core.EndomorphismEquationLoci A B n P L R)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert
