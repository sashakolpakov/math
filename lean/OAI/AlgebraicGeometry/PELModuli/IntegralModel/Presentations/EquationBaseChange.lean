import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.FixedFamilyEquations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Equation Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EquationBaseChange

noncomputable section

/-! Actual projective presentations and fixed equation loci under
arbitrary parameter base change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def e34ProjectivePresentationBaseChange {S T : Scheme} {X : Over S}
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (f : T ⟶ S) :
    HilbertScheme.Presentations.Has.Core.ProjectivePresentation ((Over.pullback f).obj X) :=
  Parameter.e34ProjectivePresentationOfNative ((Parameter.nativeProjectivePresentationOfPresentations B).baseChange f)

theorem fixed_relative_equation_iff_pullback {S : Scheme} {X Y : Over S}
    (T : Over S) (l r : X ⟶ Y) :
    (prod.snd : T ⨯ X ⟶ X) ≫ l = (prod.snd : T ⨯ X ⟶ X) ≫ r ↔
      (Over.pullback T.hom).map l = (Over.pullback T.hom).map r := by
  rw [← IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv_map X Y T l,
    ← IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv_map X Y T r]
  exact (IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv X Y T).injective.eq_iff

theorem exists_e34_fixed_pullback_equation_locus
    {S : Scheme.{0}} [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (hPresentations : Hilbert.EndomorphismEquationsInput.{0}) (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A)
    {X Y : Over S} [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsSeparated Y.hom] {m : ℕ} (l r : Fin m → (X ⟶ Y)) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧
      (∀ i, (Over.pullback Z.hom).map (l i) = (Over.pullback Z.hom).map (r i)) ∧
      ∀ T : Over S,
        (∀ i, (Over.pullback T.hom).map (l i) = (Over.pullback T.hom).map (r i)) ↔
          ∃! _f : T ⟶ Z, True := by
  obtain ⟨Z, hZ, hU, hclass⟩ := FixedFamilyEquations.exists_e34_fixed_relative_equation_locus A hPresentations BA l r
  have heq (T : Over S) := forall_congr' (fun i => fixed_relative_equation_iff_pullback T (l i) (r i))
  exact ⟨Z, hZ, (heq Z).mp hU, fun T => (heq T).symm.trans (hclass T)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EquationBaseChange
