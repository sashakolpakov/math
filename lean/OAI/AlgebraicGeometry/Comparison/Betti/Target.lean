import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence
import OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter
import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology

/-! # Target -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Target

noncomputable section

/-!
The repaired BettiComparison target refers to the constructed comparison map. Algebraic
filtration comes from degree truncation of the actual sheaf complex. On a
projective presentation, Betti filtration comes from the independently defined
subspaces of classes represented by closed forms of the specified bidegrees.
No comparison property is assumed by these definitions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

abbrev algebraicHodgeFiltration := NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66

def projectivePresentation (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := X.left
  structureMap := X.hom
  projective := P
  smooth := inferInstance

/-- A genuine pure Betti subspace, with its cohomological degree identified. -/
def projectivePureBettiInDegree (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (p : Fin (n + 1)) :
    Submodule ℂ (P.complexCohomology n) :=
  (P.pureBettiSubspace p (n - p)).map
    ((eqToHom (congrArg P.complexCohomology
      (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt)))) :
        P.complexCohomology (p + (n - p)) ⟶ P.complexCohomology n).hom

/-- The ordinary Hodge filtration on genuine projective Betti cohomology. -/
def projectiveBettiHodgeFiltration (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (r : ℤ) :
    Submodule ℂ (P.complexCohomology n) :=
  if r ≤ 0 then ⊤ else if (n : ℤ) < r then ⊥ else
    ⨆ (p : Fin (n + 1)) (_ : r ≤ (p : ℤ)), projectivePureBettiInDegree P n p

/-- The same constructed comparison, with the canonical universe lift removed. -/
def smoothDeRhamBettiLinearMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] (n : ℕ) :
    Algebraic.Sheaves.algebraicDeRham X n →ₗ[ℂ] Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n :=
  (Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n).toLinearMap.comp (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n).hom

/-- Isomorphism and naturality under smooth proper hypotheses, and compatibility
with the genuine Hodge filtrations for every projective presentation. -/
def ComparisonTarget : Prop :=
  (∀ (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsProper X.hom] (n : ℕ),
    IsIso (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n)) ∧
  (∀ (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsProper X.hom]
    [Smooth Y.hom] [IsProper Y.hom] (f : X ⟶ Y) (n : ℕ),
      OpenForms.algebraicDeRhamPullback f n ≫ Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n =
        Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap Y n ≫ Algebraic.Sheaves.bettiPullback f n) ∧
  (∀ (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsProper X.hom]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (n : ℕ) (r : ℤ),
      (algebraicHodgeFiltration X n r).map (smoothDeRhamBettiLinearMap X n) =
        projectiveBettiHodgeFiltration (projectivePresentation X P) n r)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Target
