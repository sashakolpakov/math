import OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonicTypes
import OAI.Analysis.HodgeTheory.Decomposition.SmoothHarmonic

/-! # Component Harmonic -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonic.Constructions

noncomputable section

/-! The actual componentwise smooth harmonic and Green parts. A harmonic
form in the Laplacian range vanishes, giving uniqueness of the harmonic part. -/

theorem projective_harmonic_laplacian_range_zero (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)
    (h b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hh : AdjointAlgebra.Constructions.projectivePositiveLaplacian V n h = 0) (hb : AdjointAlgebra.Constructions.projectivePositiveLaplacian V n b = h) : h = 0 := by
  obtain ⟨hd, hδ⟩ := (AdjointAlgebra.Constructions.projectivePositiveLaplacian_eq_zero_iff V n h).mp hh
  have hp := AdjointAlgebra.Constructions.projectivePositiveLaplacian_pair V n b h
  rw [hb, hδ, hd, AdjointAlgebra.Constructions.projectiveL2Pair_zero_right, AdjointAlgebra.Constructions.projectiveL2Pair_zero_right, add_zero] at hp
  exact Form.Constructions.projectiveL2Pair_definite V (n + 1) h hp

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  [∀ C : irreducibleComponents X.carrier, MeasurableSpace (X.componentVariety C).analyticSpace]
  [∀ C : irreducibleComponents X.carrier, BorelSpace (X.componentVariety C).analyticSpace] (n : ℕ)

def componentSmoothHarmonicPart (a : X.componentForms (n + 1)) : X.componentForms (n + 1) :=
  fun C => SmoothHarmonic.Constructions.projectiveSmoothHarmonicPart (X.componentVariety C) n (a C)

def componentSmoothGreen (a : X.componentForms (n + 1)) : X.componentForms (n + 1) :=
  fun C => SmoothHarmonic.Constructions.projectiveSmoothGreen (X.componentVariety C) n (a C)

theorem componentSmoothHarmonicPart_harmonic (a : X.componentForms (n + 1)) :
    ComponentLaplacian.Constructions.componentPositiveLaplacian X n (componentSmoothHarmonicPart X n a) = 0 := by
  funext C
  exact (AdjointAlgebra.Constructions.projectivePositiveLaplacian_eq_zero_iff (X.componentVariety C) n _).mpr
    (SmoothHarmonic.Constructions.projectiveSmoothHarmonicPart_closed_coclosed (X.componentVariety C) n (a C))

theorem componentSmoothGreen_laplacian (a : X.componentForms (n + 1)) :
    ComponentLaplacian.Constructions.componentPositiveLaplacian X n (componentSmoothGreen X n a) = a - componentSmoothHarmonicPart X n a := by
  funext C
  exact SmoothHarmonic.Constructions.projectiveSmoothGreen_laplacian (X.componentVariety C) n (a C)

theorem component_harmonic_laplacian_range_zero (h b : X.componentForms (n + 1))
    (hh : ComponentLaplacian.Constructions.componentPositiveLaplacian X n h = 0) (hb : ComponentLaplacian.Constructions.componentPositiveLaplacian X n b = h) : h = 0 := by
  funext C
  exact projective_harmonic_laplacian_range_zero (X.componentVariety C) n (h C) (b C)
    (congrFun hh C) (congrFun hb C)

theorem componentSmoothHarmonicPart_projection_zero (i : Core.Constructions.Bidegree (n + 1)) (a : X.componentForms (n + 1))
    (ha : Projectors.Constructions.componentProjection X (n + 1) i a = 0) :
    Projectors.Constructions.componentProjection X (n + 1) i (componentSmoothHarmonicPart X n a) = 0 := by
  apply component_harmonic_laplacian_range_zero X n _ (-Projectors.Constructions.componentProjection X (n + 1) i (componentSmoothGreen X n a))
  · exact ComponentHarmonicTypes.Constructions.componentProjection_harmonic X n i _ (componentSmoothHarmonicPart_harmonic X n a)
  · rw [map_neg, ComponentHarmonicTypes.Constructions.componentPositiveLaplacian_projection, componentSmoothGreen_laplacian,
      map_sub, ha, zero_sub, neg_neg]

theorem componentSmoothHarmonicPart_pure (i : Core.Constructions.Bidegree (n + 1)) (a : X.componentForms (n + 1))
    (ha : a ∈ Core.Constructions.pureFormsAt X (n + 1) i) : componentSmoothHarmonicPart X n a ∈ Core.Constructions.pureFormsAt X (n + 1) i := by
  have hz (j : Core.Constructions.Bidegree (n + 1)) (hji : j ≠ i) :
      Projectors.Constructions.componentProjection X (n + 1) j (componentSmoothHarmonicPart X n a) = 0 := by
    apply componentSmoothHarmonicPart_projection_zero X n j a
    rw [ComponentRotation.Constructions.componentProjection_on_pure X (n + 1) j i a ha, ite_eq_right hji]
  have heq : componentSmoothHarmonicPart X n a =
      Projectors.Constructions.componentProjection X (n + 1) i (componentSmoothHarmonicPart X n a) := by
    conv_lhs => rw [← Projectors.Constructions.sum_componentProjection X (n + 1) (componentSmoothHarmonicPart X n a)]
    exact Finset.sum_eq_single i (fun j _ hji => hz j hji) (fun hi => (hi (Finset.mem_univ i)).elim)
  rw [heq]
  exact Projectors.Constructions.componentProjection_pure X (n + 1) i _

end

end OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonic.Constructions
