import OAI.NumberTheory.ArithmeticGroups.Lattices.IntrinsicUnipotentProjection
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.TriangularConjugates

/-! # Upper Split Conjugation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

section

/-! Intrinsic split exponentials act by conjugation on the full
ambient upper unipotent group. -/

def Ambient.UpperSplitConjugation.Construction.diagonalUpperConjugation {m : ℕ} (a : (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (d : Fin m → ℝ) (hd : ∀ i, d i ≠ 0) (ha : a.val = Matrix.diagonal d) :
    UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m →* UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m where
  toFun n := ⟨a * n.val * a⁻¹, by
    change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (a.val * n.val.val * (a⁻¹).val)
    rw [Compact.TriangularConjugates.Construction.diagonal_matrix_unit_inverse a d hd ha, ha]
    exact n.property.diagonal_conjugation d hd⟩
  map_one' := by
    apply Subtype.ext
    change a * 1 * a⁻¹ = 1
    group
  map_mul' n m := by
    apply Subtype.ext
    change a * (n.val * m.val) * a⁻¹ = (a * n.val * a⁻¹) * (a * m.val * a⁻¹)
    group

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def KillingSplit.Construction.KillingSplitWeightData.ambientSplitMatrixUnit (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    (Matrix (Fin (Module.finrank ℝ L)) (Fin (Module.finrank ℝ L)) ℝ)ˣ :=
  ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis (OperatorExponentialUnits.Construction.operatorExpUnit A.val)

theorem KillingSplit.Construction.KillingSplitWeightData.ambientSplitMatrixUnit_val (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    (d.ambientSplitMatrixUnit A).val = Matrix.diagonal (fun i => Real.exp (d.weight i A)) :=
  d.exponential_matrix A

def KillingSplit.Construction.KillingSplitWeightData.ambientUpperConjugation (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L) →*
      UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L) :=
  Ambient.UpperSplitConjugation.Construction.diagonalUpperConjugation (d.ambientSplitMatrixUnit A) (fun i => Real.exp (d.weight i A))
    (fun i => Real.exp_ne_zero (d.weight i A)) (d.ambientSplitMatrixUnit_val A)

theorem KillingSplit.Construction.KillingSplitWeightData.ambientUpperConjugation_val (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace)
    (n : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L)) :
    (d.ambientUpperConjugation A n).val = d.ambientSplitMatrixUnit A * n.val * (d.ambientSplitMatrixUnit A)⁻¹ := rfl

theorem KillingSplit.Construction.KillingSplitWeightData.ambientPositiveConjugation_exp_unit (d : KillingSplit.Construction.KillingSplitWeightData B)
    (A : d.subspace) (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)) :
    OperatorExponentialUnits.Construction.operatorExpUnit (d.ambientPositiveConjugation A X).val =
      OperatorExponentialUnits.Construction.operatorExpUnit A.val * OperatorExponentialUnits.Construction.operatorExpUnit X.val * (OperatorExponentialUnits.Construction.operatorExpUnit A.val)⁻¹ := by
  apply Units.ext
  change NormedSpace.exp (d.ambientPositiveConjugation A X).val =
    NormedSpace.exp A.val * NormedSpace.exp X.val * NormedSpace.exp (-A.val)
  rw [d.ambientPositiveConjugation_val, Split.ConjugationBracketOperators.Construction.exponential_conjugation_exp]

theorem KillingSplit.Construction.KillingSplitWeightData.unipotentConjugation_unit (d : KillingSplit.Construction.KillingSplitWeightData B)
    (A : d.subspace) (n : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    (d.unipotentConjugation A n).val = OperatorExponentialUnits.Construction.operatorExpUnit A.val * n.val * (OperatorExponentialUnits.Construction.operatorExpUnit A.val)⁻¹ := by
  apply Units.ext
  exact d.unipotentConjugation_val A n

end

/-! The intrinsic unipotent projection commutes with every split
conjugation when the regular element separates distinct weights. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L} {d : KillingSplit.Construction.KillingSplitWeightData B}
  {hd : Antitone (fun i => d.weight i d.regularElement)}

def Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.complementConjugation (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (A : d.subspace) (X : p.complement) : p.complement :=
  ⟨d.ambientPositiveConjugation A X.val, p.invariant A X.val X.property⟩

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.product_split_conjugation (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (A : d.subspace)
    (q : (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection (fun i => d.weight i d.regularElement) hd).range ×
      (p.complement × UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))) :
    d.ambientUpperConjugation A (p.product q) =
      p.product (q.1, (p.complementConjugation A q.2.1, d.unipotentConjugation A q.2.2)) := by
  let a := d.ambientSplitMatrixUnit A
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis
  have h0 : q.1.val.val * a = a * q.1.val.val := by
    apply Units.ext
    exact (d.zeroWeightBlock_commutes_exponential hd hsep q.1 A).eq
  apply Subtype.ext
  rw [d.ambientUpperConjugation_val, p.product_val, p.product_val]
  change a * (q.1.val.val * F (OperatorExponentialUnits.Construction.operatorExpUnit q.2.1.val.val) * F q.2.2.val) * a⁻¹ =
    q.1.val.val * F (OperatorExponentialUnits.Construction.operatorExpUnit (d.ambientPositiveConjugation A q.2.1.val).val) *
      F (d.unipotentConjugation A q.2.2).val
  rw [d.ambientPositiveConjugation_exp_unit, d.unipotentConjugation_unit]
  simp only [map_mul, map_inv]
  change a * (q.1.val.val * F (OperatorExponentialUnits.Construction.operatorExpUnit q.2.1.val.val) * F q.2.2.val) * a⁻¹ =
    q.1.val.val * (a * F (OperatorExponentialUnits.Construction.operatorExpUnit q.2.1.val.val) * a⁻¹) * (a * F q.2.2.val * a⁻¹)
  calc
    a * (q.1.val.val * F (OperatorExponentialUnits.Construction.operatorExpUnit q.2.1.val.val) * F q.2.2.val) * a⁻¹ =
      (a * q.1.val.val) * F (OperatorExponentialUnits.Construction.operatorExpUnit q.2.1.val.val) * F q.2.2.val * a⁻¹ := by group
    _ = _ := by rw [← h0]; group

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.intrinsicProjection_split_conjugation (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (A : d.subspace) (g : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L)) :
    p.intrinsicProjection (d.ambientUpperConjugation A g) =
      d.unipotentConjugation A (p.intrinsicProjection g) := by
  obtain ⟨q, rfl⟩ := p.product.surjective g
  rw [p.product_split_conjugation hsep]
  simp only [Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.intrinsicProjection, Homeomorph.symm_apply_apply]

theorem KillingSplit.Construction.KillingSplitWeightData.unipotentConjugation_one (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    d.unipotentConjugation A 1 = 1 := by
  apply Subtype.ext
  rw [d.unipotentConjugation_unit]
  change OperatorExponentialUnits.Construction.operatorExpUnit A.val * 1 * (OperatorExponentialUnits.Construction.operatorExpUnit A.val)⁻¹ = 1
  group

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.projection_fiber_split_invariant (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (A : d.subspace) (g : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L))
    (hg : p.intrinsicProjection g = 1) : p.intrinsicProjection (d.ambientUpperConjugation A g) = 1 := by
  rw [p.intrinsicProjection_split_conjugation hsep, hg, d.unipotentConjugation_one]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
