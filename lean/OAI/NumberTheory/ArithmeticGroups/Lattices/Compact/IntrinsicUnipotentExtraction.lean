import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.UpperSplitConjugation

/-! # Intrinsic Unipotent Extraction -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! A compact bound for a mixed unipotent product bounds its
intrinsic split-conjugated factor. The argument uses inversion and
the continuous intrinsic coordinate of the ambient product. -/

open scoped Pointwise

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L} {d : KillingSplit.Construction.KillingSplitWeightData B}
  {hd : Antitone (fun i => d.weight i d.regularElement)}

theorem KillingSplit.Construction.KillingSplitWeightData.unipotentConjugation_inv (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace)
    (n : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    d.unipotentConjugation A n⁻¹ = (d.unipotentConjugation A n)⁻¹ := by
  apply Subtype.ext
  rw [d.unipotentConjugation_unit]
  change OperatorExponentialUnits.Construction.operatorExpUnit A.val * n.val⁻¹ * (OperatorExponentialUnits.Construction.operatorExpUnit A.val)⁻¹ =
    ((d.unipotentConjugation A n).val)⁻¹
  rw [d.unipotentConjugation_unit]
  group

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.compact_intrinsic_factor_extraction
    (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (C : Set (Matrix (Fin (Module.finrank ℝ L)) (Fin (Module.finrank ℝ L)) ℝ)ˣ)
    (hC : IsCompact C) :
    ∃ S : Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)), IsCompact S ∧
      ∀ (A : d.subspace) (v : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L))
        (n : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)),
        p.intrinsicProjection v = 1 →
        d.ambientSplitMatrixUnit A * (d.intrinsicUpperInclusion hd n).val * v.val⁻¹ *
          (d.ambientSplitMatrixUnit A)⁻¹ ∈ C → d.unipotentConjugation A n ∈ S := by
  let D : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L)) := Subtype.val ⁻¹' C⁻¹
  have hD : IsCompact D := (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup_isClosed (Module.finrank ℝ L)).isClosedEmbedding_subtypeVal.isCompact_preimage hC.inv
  let S := (fun q => (p.intrinsicProjection q)⁻¹) '' D
  refine ⟨S, hD.image p.intrinsicProjection_continuous.inv, fun A v n hv hn => ?_⟩
  let q := d.ambientUpperConjugation A (v * d.intrinsicUpperInclusion hd n⁻¹)
  have hq : q ∈ D := by
    change q.val ∈ C⁻¹
    apply Set.mem_inv.mpr
    have he : q.val⁻¹ = d.ambientSplitMatrixUnit A * (d.intrinsicUpperInclusion hd n).val * v.val⁻¹ *
        (d.ambientSplitMatrixUnit A)⁻¹ := by
      rw [d.ambientUpperConjugation_val]
      change (d.ambientSplitMatrixUnit A *
        (v.val * (d.intrinsicUpperInclusion hd n⁻¹).val) * (d.ambientSplitMatrixUnit A)⁻¹)⁻¹ = _
      rw [map_inv]
      change (d.ambientSplitMatrixUnit A *
        (v.val * (d.intrinsicUpperInclusion hd n).val⁻¹) * (d.ambientSplitMatrixUnit A)⁻¹)⁻¹ = _
      group
    rw [he]
    exact hn
  refine ⟨q, hq, ?_⟩
  change (p.intrinsicProjection (d.ambientUpperConjugation A
    (v * d.intrinsicUpperInclusion hd n⁻¹)))⁻¹ = _
  rw [p.intrinsicProjection_split_conjugation hsep, p.intrinsicProjection_right_mul, hv, one_mul,
    d.unipotentConjugation_inv, inv_inv]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
