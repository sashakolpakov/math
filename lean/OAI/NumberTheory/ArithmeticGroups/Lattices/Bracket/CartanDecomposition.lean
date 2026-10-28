import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.PolarDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketLogarithm

/-! # Cartan Decomposition -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanDecomposition.Construction

noncomputable section

/-! An adjoint-stable bracket automorphism factors as an orthogonal
bracket automorphism times the exponential of a self-adjoint derivation. -/

open _root_.ContinuousLinearMap NormedSpace

theorem bracket_automorphism_cartan_decomposition
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (g : L ≃L[ℝ] L)
    (hg : ContinuousBracketChange.Construction.continuousBracketChange g B = B)
    (hadj : ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
      B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y)) :
    ∃ (k : L ≃L[ℝ] L) (D : L →L[ℝ] L),
      ContinuousBracketChange.Construction.continuousBracketChange k B = B ∧
      (∀ x y, inner ℝ (k x) (k y) = inner ℝ x y) ∧ D.toLinearMap.IsSymmetric ∧
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B D = 0 ∧ g.toContinuousLinearMap = k.toContinuousLinearMap * exp D := by
  obtain ⟨k, s, hgs, hk, hs, hki, hsSym, hsPos⟩ :=
    PolarDecomposition.Construction.bracket_automorphism_polar_decomposition B g hg hadj
  obtain ⟨D, hDSym, hDB, hD⟩ := Positive.BracketLogarithm.Construction.positive_bilinear_preserver_logarithm B s.toContinuousLinearMap
    hsSym hsPos ((PolarDecomposition.Construction.continuousBracketChange_eq_self_iff B s).mp hs)
  refine ⟨k, D, hk, hki, hDSym, hDB, ?_⟩
  rw [hgs, hD]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanDecomposition.Construction
