import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.PermutedMixedProduct
import OAI.NumberTheory.ArithmeticGroups.Lattices.IntrinsicIwasawaQRUnits
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.IntrinsicUnipotentExtraction

/-! # Intrinsic Conjugated Unipotent Bound -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! First intrinsic translated-intersection bound: after removing
the intrinsic right factor of the fixed ambient unipotent, the
split-conjugated intrinsic unipotent coordinate remains compact. -/

open _root_.ContinuousLinearMap

theorem KillingSplit.Construction.KillingSplitWeightData.compact_intrinsic_conjugated_unipotent_factors
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement)) (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (C : Set (Matrix (Fin (Module.finrank ℝ L)) (Fin (Module.finrank ℝ L)) ℝ)ˣ) (hC : IsCompact C)
    (htri : ∀ n ∈ C, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular n.val) (t : ℝ) (ht : 0 ≤ t)
    (σ : Equiv.Perm (Fin (Module.finrank ℝ L))) :
    ∃ S : Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)), IsCompact S ∧
      ∀ (k a : (L →L[ℝ] L)ˣ) (v : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L))
        (r : Fin (Module.finrank ℝ L) → ℝ),
        ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis k.val ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ L)) ℝ →
        (∀ i, 0 < r i) → ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis a.val = Matrix.diagonal r →
        (∀ i j, i.val + 1 = j.val → Real.log (r i) - Real.log (r j) ≤ t) →
        p.intrinsicProjection v = 1 → ∀ n ∈ C,
        let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis
        let g := k * a * F.symm n * F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ) * F.symm v.val
        g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B →
        ∃ k₁ : OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ A : d.subspace,
          ∃ n₁ : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement),
            g = k₁.val * OperatorExponentialUnits.Construction.operatorExpUnit A.val * n₁.val ∧ d.unipotentConjugation A n₁ ∈ S := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis
  obtain ⟨D, hD, hbound⟩ := Compact.PermutedMixedProduct.Construction.compact_permuted_siegel_mixed_products d.basis C hC htri t ht σ
  obtain ⟨S, hS, hExtract⟩ := p.compact_intrinsic_factor_extraction hsep D hD
  refine ⟨S, hS, fun k a v r hk hr ha hstep hv n hn hg => ?_⟩
  let g := k * a * F.symm n * F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ) * F.symm v.val
  obtain ⟨k₁, A, n₁, he, hAQ, hU⟩ := d.intrinsic_iwasawa_qr_units hd hadj hDadj g hg
  have hv' : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis (F.symm v.val).val) := by
    change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (F (F.symm v.val)).val
    rw [F.apply_symm_apply]
    exact v.property
  have hNorm := hbound k a (F.symm v.val) r hk hr ha hstep hv' n hn
  change QRPositiveUnit.Construction.operatorQRPositiveDiagonalUnit d.basis g * OperatorQRVal.Construction.operatorQRUnipotentUnit d.basis g *
    (F (F.symm v.val))⁻¹ * (QRPositiveUnit.Construction.operatorQRPositiveDiagonalUnit d.basis g)⁻¹ ∈ D at hNorm
  rw [F.apply_symm_apply, hAQ, hU] at hNorm
  refine ⟨k₁, A, n₁, he, ?_⟩
  exact hExtract A v n₁ hv hNorm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
