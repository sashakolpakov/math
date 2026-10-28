import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveGenerationBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ComplementInduction

/-! # Generation On Closed -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.GenerationOnClosed.BundleCycles

noncomputable section

/-! The closed-support induction assertion allows every actual
base morphism, including nonreduced and reducible closed bases. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {E X Y : Scheme.{0}} (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

def ProjectiveGenerationOnClosed (S : Closeds Y) : Prop :=
  ∀ (Z : Scheme.{0}) [AlgebraicGeometry.IsNoetherian Z] [Z.IsSeparated]
    (i : Z ⟶ Y) [IsClosedImmersion i], Set.range i = (S : Set Y) →
    ∀ (b : Z ⟶ X) (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
      (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd p b ≫ f) d),
      α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd p b) f r (hp.baseChange b) (L.pullback (pullback.fst p b)) d

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.GenerationOnClosed.BundleCycles
