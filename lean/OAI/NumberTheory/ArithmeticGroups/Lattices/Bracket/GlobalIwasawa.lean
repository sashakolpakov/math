import OAI.NumberTheory.ArithmeticGroups.Lattices.GlobalSplitFilteredProduct
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredUnipotentDecomposition

/-! # Global Iwasawa -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.GlobalIwasawa.Construction

noncomputable section

/-! Global compact/split/unipotent factorization for adjoint-stable
bracket automorphism groups, and its existence for real Killing brackets. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.ContinuousLinearMap

theorem bracket_global_iwasawa_product
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (a : Submodule ℝ (L →L[ℝ] L)) (H : L →L[ℝ] L)
    (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) (hH : H ∈ a)
    (hsum : DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B = DerivationSpectralDecomposition.Construction.skewBracketDerivations B ⊔ a ⊔ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H)
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    ∃ k ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ A ∈ a, ∃ n ∈ UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B b w,
      g = k * OperatorExponentialUnits.Construction.operatorExpUnit A * n := by
  obtain ⟨k, hk, p, hp, hprod⟩ := GlobalSplitFilteredProduct.Construction.bracket_global_splitFiltered_product B hadj a H ha hc hH hsum b w heig g hg
  obtain ⟨A, hA, n, hn, hpdec⟩ := Split.FilteredUnipotentDecomposition.Construction.splitFiltered_bracket_decomposition B b w H a ha hc hH heig p hp
  refine ⟨k, hk, A, hA, n, hn, ?_⟩
  rw [← hprod, hpdec, mul_assoc]

theorem exists_killing_bracket_global_iwasawa_realization
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] V) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ (m : ℕ) (Ψ : V ≃L[ℝ] EuclideanSpace ℝ (Fin m))
      (a : Submodule ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
      (b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) (w : Fin m → ℝ),
      a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule (Positive.Killing.Construction.continuousBracketTransport Ψ B) ∧
      (∀ X ∈ a, ∀ Y ∈ a, Commute X Y) ∧
      IsCompact (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup (Positive.Killing.Construction.continuousBracketTransport Ψ B) :
        Set (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))ˣ) ∧
      IsClosed (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup (Positive.Killing.Construction.continuousBracketTransport Ψ B) b w :
        Set (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))ˣ) ∧
      ∀ g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup (Positive.Killing.Construction.continuousBracketTransport Ψ B),
        ∃ k ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup (Positive.Killing.Construction.continuousBracketTransport Ψ B), ∃ A ∈ a,
          ∃ n ∈ UnipotentBracketGroup.Construction.unipotentBracketUnitGroup (Positive.Killing.Construction.continuousBracketTransport Ψ B) b w,
            g = k * OperatorExponentialUnits.Construction.operatorExpUnit A * n := by
  obtain ⟨m, Ψ, hadj, hDadj⟩ := AutomorphismAdjointDerivations.Construction.exists_normed_killing_adjoint_stable_realization B hB hK
  obtain ⟨a, H, ha, hc, hH, hsum⟩ := LinearIwasawaDecomposition.Construction.exists_bracket_linear_iwasawa_decomposition (Positive.Killing.Construction.continuousBracketTransport Ψ B) hDadj
  have hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
  let b := (ha hH).1.eigenvectorBasis hm
  let w := (ha hH).1.eigenvalues hm
  have heig (i : Fin m) : H (b i) = w i • b i := (ha hH).1.apply_eigenvectorBasis hm i
  exact ⟨m, Ψ, a, b, w, ha, hc, OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup_isCompact _,
    UnipotentBracketGroup.Construction.unipotentBracketUnitGroup_isClosed _ b w, fun g hg =>
      bracket_global_iwasawa_product (Positive.Killing.Construction.continuousBracketTransport Ψ B) hadj a H ha hc hH hsum b w heig g hg⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.GlobalIwasawa.Construction
