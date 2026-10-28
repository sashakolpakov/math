import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalSiegelBruhatReduction
import OAI.NumberTheory.ArithmeticGroups.Lattices.IntrinsicConjugatedUnipotentBound

/-! # Normalized Intersection Split Factors -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! A translated ambient region with its intrinsic right factor
removed has a compact factor before every intrinsic split diagonal. -/

open _root_.ContinuousLinearMap

theorem KillingSplit.Construction.KillingSplitWeightData.normalized_intersection_compact_split_factors
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement)) (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L))) (hC : IsCompact C)
    (t : ℝ) (ht : 0 ≤ t) (σ : Equiv.Perm (Fin (Module.finrank ℝ L)))
    (v : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L)) (hv : p.intrinsicProjection v = 1) :
    ∃ Q : Set (L →L[ℝ] L)ˣ, IsCompact Q ∧ ∀ g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B,
      g.val ∈ OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet d.basis (PermutationMatrixUnits.Construction.permutationMatrixUnit σ * v.val) t C →
      ∃ k : OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ A : d.subspace, ∃ q ∈ Q,
        g.val = k.val * q * OperatorExponentialUnits.Construction.operatorExpUnit A.val := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis
  obtain ⟨S, hS, hBound⟩ := d.compact_intrinsic_conjugated_unipotent_factors hd p hsep hadj hDadj
    (Subtype.val '' C) (hC.image continuous_subtype_val)
    (by rintro _ ⟨n, _, rfl⟩; exact n.property) t ht σ
  refine ⟨Subtype.val '' S, hS.image continuous_subtype_val, ?_⟩
  rintro g ⟨k, x, n, hn, hk, hx, hg⟩
  let a := F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x)
  have ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis a.val = Matrix.diagonal (fun i => Real.exp (x i)) := by
    change (F a).val = _
    rw [F.apply_symm_apply]
    rfl
  have hgap : ∀ i j, i.val + 1 = j.val → Real.log (Real.exp (x i)) - Real.log (Real.exp (x j)) ≤ t := by
    simpa only [Real.log_exp] using hx
  have he : g.val = k * a * F.symm n.val * F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ) * F.symm v.val := by
    rw [hg]
    change k * F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * (PermutationMatrixUnits.Construction.permutationMatrixUnit σ * v.val)) = _
    simp only [map_mul, a, mul_assoc]
  obtain ⟨k₁, A, n₁, hI, hIn⟩ := hBound k a v (fun i => Real.exp (x i)) hk (fun i => Real.exp_pos _) ha hgap hv
    n.val ⟨n, hn, rfl⟩ (by rw [← he]; exact g.property)
  refine ⟨k₁, A, (d.unipotentConjugation A n₁).val, ⟨_, hIn, rfl⟩, ?_⟩
  rw [he, hI, d.unipotentConjugation_unit]
  group

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
