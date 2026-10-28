import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphTwistingSquare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.PolynomialPowers

/-! # Zero Graph Field Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ZeroGraphFieldBound

noncomputable section

/-! A proved polynomial bound for the zero graph yields a single polynomial for every field-valued polarized isomorphism graph over the same base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

local instance zeroBoundPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))
local instance zeroBoundPullbackFP {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))
local instance zeroBoundPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

theorem polarized_fieldGraphBound_of_zeroGraph
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle A.graphBundle B.graphBundle)
      (A.abelian.scheme ⊗ B.abelian.scheme).hom)
    (Q : Polynomial ℚ)
    (hQ : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (E.relativeMorphism A.graphBundle B.graphBundle) Q
      (1 : A.abelian.scheme ⟶ B.abelian.scheme)) :
    ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S)
      (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback s) (B.pullback s)),
      Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding s
        (E.relativeMorphism A.graphBundle B.graphBundle))
        (Q.comp (Polynomial.C (2 : ℚ) * Polynomial.X)) e.abelian.hom := by
  let j := E.relativeMorphism A.graphBundle B.graphBundle
  intro K _ s e
  have hp := hQ.baseChange j Q s
  have hzero : (Over.pullback s).map (1 : A.abelian.scheme ⟶ B.abelian.scheme) = 1 :=
    Functor.map_one (Over.pullback s)
  rw [hzero] at hp
  have hW : (GraphTwistingSquare.polarizedZeroGraphTwistingBundle A B E s).HasSectionHilbertPolynomial
      (A.pullback s).abelian.scheme.hom Q :=
    (Relative.EmbeddingIntrinsic.embeddedGraph_intrinsicHilbertPolynomial_iff (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding s j) Q 1).mp hp
  apply (Relative.EmbeddingIntrinsic.embeddedGraph_intrinsicHilbertPolynomial_iff (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding s j) _ e.abelian.hom).mpr
  exact (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso (A.pullback s).abelian.scheme.hom
    _ _ (GraphTwistingSquare.polarizedIsoGraphTwistingSquareIso A B E s e) _).mpr (hW.tensorPower 2 (by decide))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ZeroGraphFieldBound
