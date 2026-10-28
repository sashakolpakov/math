import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IntegrationComplex
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup

/-! # Packed Eliminate -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedEliminate.CM.Construction

noncomputable section

/-! Eliminate a nonzero top factor from an arbitrary packed even class. -/

open _root_.CategoryTheory CartesianMonoidalCategory

theorem packed_algebraic_of_top_factor (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput)
    (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (a : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver))
    (b : S.complexCohomology (S.complexDimension + S.complexDimension)) (hb : b ≠ 0)
    (halg : PackedRegroup.CM.Construction.IsAlgebraicEven (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
      (PackedRegroup.CM.Construction.evenPullback (snd S.toOver X.toOver) a *
        PackedRegroup.CM.Construction.evenPullback (fst S.toOver X.toOver)
          (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace S.toOver) S.complexDimension b))) :
    PackedRegroup.CM.Construction.IsAlgebraicEven X a := by
  rcases a with ⟨p, a⟩
  change a ∈ X.complexGeometricAlgebraicClasses p
  by_cases ha : a = 0
  · rw [ha]
    exact Submodule.zero_mem _
  have hp : p ≤ X.complexDimension := by
    have h := Kunneth.CM.SurfaceConstruction.complex_degree_le X (p + p) a ha
    omega
  exact IntegrationComplex.CM.Construction.algebraic_of_top_factor h_Functoriality S X p hp a b hb halg

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedEliminate.CM.Construction
