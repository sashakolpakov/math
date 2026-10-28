import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ZeroGraphFieldBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.GraphFieldCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.ParameterPointMap

/-! # Zero Graph Universal Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ZeroGraphUniversalBound

noncomputable section

/-! A zero-graph Hilbert polynomial gives an actual uniform bound for all polarized isomorphism graphs on every test scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

local instance zeroUniversalPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))
local instance zeroUniversalPullbackFP {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))
local instance zeroUniversalPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

theorem polarized_universalGraphBound_of_zeroGraph
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle A.graphBundle B.graphBundle)
      (A.abelian.scheme ⊗ B.abelian.scheme).hom)
    (Q : Polynomial ℚ)
    (hQ : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (E.relativeMorphism A.graphBundle B.graphBundle) Q
      (1 : A.abelian.scheme ⟶ B.abelian.scheme)) (T : Over S)
    (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom)) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom
      (E.relativeMorphism A.graphBundle B.graphBundle))
      (Q.comp (Polynomial.C (2 : ℚ) * Polynomial.X)) e.abelian.hom := by
  apply Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.of_geometricFieldBaseChanges
    (E.relativeMorphism A.graphBundle B.graphBundle) _ T e.abelian.hom
  intro K _ s
  let c : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s rfl
  have h := ZeroGraphFieldBound.polarized_fieldGraphBound_of_zeroGraph A B E Q hQ K (s ≫ T.hom)
    (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c e)
  rw [Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ZeroGraphUniversalBound
