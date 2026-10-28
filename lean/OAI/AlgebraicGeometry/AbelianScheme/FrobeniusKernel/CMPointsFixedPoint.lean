import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsPointLieRanks

/-! # CM Points Fixed Point -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsFixedPoint.Construction

noncomputable section

/-!
Native fixed-point conclusions of the full CMPoints conditional input.
Good moduli classification is recovered from the actual model
predicate; the active and compact Lie ranks come from CMPoints's
geometric conclusions via the constructed field and point adapters.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable (M : PELModuli.CMPoints.Models.RankThreePELModel E K) {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
variable (R : M.GoodIntegralReduction q j)

/-- The full CMPoints conclusion supplies the native active and compact
Lie ranks at every fixed-field geometric point. -/
theorem l45GeometricConclusion_fixedLieRanks (h : CMPoints.Construction.GeometricConclusion R) :
    ∃ chosen : Set Gal(E/ℚ),
      PELModuli.CMPoints.Arithmetic.rationalConjugation E ∈ chosen ∧
      (∀ τ, τ ∈ chosen ↔ PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ ∉ chosen) ∧
      ∀ (a : M.Family) (x : ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a),
        AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).polarized.abelian
          (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).action
          (PointsPointLieRanks.Construction.l45FixedLieCharacter M (j := j) (PELModuli.CMPoints.Arithmetic.rationalConjugation E)) 1 ∧
        ∀ τ ∈ chosen, τ ≠ PELModuli.CMPoints.Arithmetic.rationalConjugation E →
          AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).polarized.abelian
            (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).action (PointsPointLieRanks.Construction.l45FixedLieCharacter M (j := j) τ) 0 ∨
          AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).polarized.abelian
            (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).action (PointsPointLieRanks.Construction.l45FixedLieCharacter M (j := j) τ) 3 := by
  obtain ⟨chosen, hc, hchosen, _, hlie⟩ := h.2
  refine ⟨chosen, hc, hchosen, fun a x => ⟨?_, ?_⟩⟩
  · exact PointsPointLieRanks.Construction.l45FixedPoint_hasLieRank M R a x (PELModuli.CMPoints.Arithmetic.rationalConjugation E) 1
      (hlie a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x)).1
  · intro τ hτ hτc
    rcases (hlie a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x)).2 τ hτ hτc with hz | hm
    · exact Or.inl (PointsPointLieRanks.Construction.l45FixedPoint_hasLieRank M R a x τ 0 hz)
    · exact Or.inr (PointsPointLieRanks.Construction.l45FixedPoint_hasLieRank M R a x τ 3 hm)

variable (hM : M.HasPrescribedBallPeriods)
variable (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
variable (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
variable (hlabels : ∀ (v : Fin M.s) (b : Bool),
  labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))

/-- The native good-moduli hypothesis is already a clause of the
actual CMPoints model predicate, rather than an added classification premise. -/
theorem l45NativeReduction_good (a : M.Family) :
    (CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a).IsGoodCompletelySplitReduction := by
  obtain ⟨_, _, _, _, _, hmoduli, _, _, _, _⟩ := hM.2.2 a
  exact hmoduli

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsFixedPoint.Construction
