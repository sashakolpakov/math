import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.UnipotentProductData

/-! # Intrinsic Unipotent Projection -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The intrinsic coordinate of the ambient unipotent product is
equivariant for right multiplication by intrinsic unipotents. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L} {d : KillingSplit.Construction.KillingSplitWeightData B}
  {hd : Antitone (fun i => d.weight i d.regularElement)}

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.product_right_mul (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (q : (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection (fun i => d.weight i d.regularElement) hd).range ×
      (p.complement × UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)))
    (n : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    p.product (q.1, (q.2.1, q.2.2 * n)) = p.product q * d.intrinsicUpperInclusion hd n := by
  apply Subtype.ext
  change (p.product (q.1, (q.2.1, q.2.2 * n))).val =
    (p.product q).val * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis n.val
  rw [p.product_val, p.product_val]
  change q.1.val.val * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis (OperatorExponentialUnits.Construction.operatorExpUnit q.2.1.val.val) *
      ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis (q.2.2.val * n.val) = _
  rw [map_mul]
  simp only [mul_assoc]

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.intrinsicProjection_right_mul (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (g : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L))
    (n : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    p.intrinsicProjection (g * d.intrinsicUpperInclusion hd n) = p.intrinsicProjection g * n := by
  obtain ⟨q, rfl⟩ := p.product.surjective g
  rw [← p.product_right_mul]
  simp only [Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.intrinsicProjection, Homeomorph.symm_apply_apply]

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.intrinsicProjection_one (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd) :
    p.intrinsicProjection 1 = 1 := by
  have he : p.product (1, (0, 1)) = 1 := by
    apply Subtype.ext
    rw [p.product_val]
    change 1 * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis (OperatorExponentialUnits.Construction.operatorExpUnit 0) *
      ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis 1 = 1
    rw [OperatorExponentialUnits.Construction.operatorExpUnit_zero, map_one, one_mul, mul_one]
  rw [← he]
  simp only [Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.intrinsicProjection, Homeomorph.symm_apply_apply]

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.intrinsicProjection_inclusion (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (n : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    p.intrinsicProjection (d.intrinsicUpperInclusion hd n) = n := by
  simpa only [one_mul, p.intrinsicProjection_one] using p.intrinsicProjection_right_mul 1 n

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.split_off_intrinsic_factor (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (g : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L)) :
    ∃ v : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L),
      p.intrinsicProjection v = 1 ∧ g = v * d.intrinsicUpperInclusion hd (p.intrinsicProjection g) := by
  refine ⟨g * d.intrinsicUpperInclusion hd (p.intrinsicProjection g)⁻¹, ?_, ?_⟩
  · rw [p.intrinsicProjection_right_mul, mul_inv_cancel]
  · rw [map_inv]
    group

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
