import OAI.RepresentationTheory.Theta.Geometric.Period.Lattice
import OAI.RepresentationTheory.Theta.Geometric.Torus.AlgebraicAction

/-! # Algebraization -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.Algebraization.ActiveHeckeThetaData

noncomputable section

/-! Algebraic abelian models of the explicit varying reference period
quotients, with their original integral CM action retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.periodIntegerAction :
    NumberField.RingOfIntegers E →+* Module.End ℂ (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :=
  D.periodScalarAction.comp (algebraMap (NumberField.RingOfIntegers E) E)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.periodIntegerAction_preserves_lattice (hg : D.pel.HasIntegralModelGeometry)
    (x : D.domain) (a : NumberField.RingOfIntegers E)
    (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) (ht : t ∈ D.periodLattice x.val) :
    D.periodIntegerAction a t ∈ D.periodLattice x.val := by
  obtain ⟨v, hv, rfl⟩ := (D.periodLattice_mem x.val t).mp ht
  rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, hL, _⟩
  apply (D.periodLattice_mem x.val _).mpr
  refine ⟨(a : E) • v, hL.2.2 a v hv, ?_⟩
  change D.periodProjection x.val (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings ((a : E) • v)) =
    D.periodScalarAction (a : E)
      (D.periodProjection x.val (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v))
  rw [← D.periodProjection_ambientAction, NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction_embedding]

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.canonicalQuotientAction (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    NumberField.RingOfIntegers E →+* AddMonoid.End (D.canonicalPeriodData hg x).periodTorus :=
  (D.canonicalPeriodData hg x).quotientRingAction D.periodIntegerAction
    (D.periodIntegerAction_preserves_lattice hg x)

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.exists_canonical_abelian_model_with_action (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    ∃ (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (e : (D.canonicalPeriodData hg x).periodTorus ≃ₘ⟮
        𝓘(ℂ, (D.canonicalPeriodData hg x).space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
      (r : NumberField.RingOfIntegers E →+* AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A.toOver),
      (∀ u v, e (u + v) = e u * e v) ∧
      ∀ a t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.toOver (r a)) (e t) =
        e (D.canonicalQuotientAction hg x a t) :=
  Torus.AlgebraicAction.exists_abelian_torus_with_ring_action (D.canonicalPeriodData hg x) D.periodIntegerAction
    (D.periodIntegerAction_preserves_lattice hg x)

end

end OAI.RepresentationTheory.Theta.Geometric.Period.Algebraization.ActiveHeckeThetaData
