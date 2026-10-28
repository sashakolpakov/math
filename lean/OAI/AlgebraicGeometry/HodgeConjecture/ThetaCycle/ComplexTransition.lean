import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodTotal

/-! # Complex Transition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComplexTransition.CM

noncomputable section

/-! ThetaCycle: the rational transition acts on the literal complex period coordinates. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM _root_.Module

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

abbrev TotalAmbient := Fin 2 → HeckeCycles.GeometricSource.CM.Ambient K

def totalEmbedding (x : TransportNew.CM.TensorPositions K) : TotalAmbient K :=
  fun i => HeckeCycles.GeometricSource.CM.embeddingCoordinates K (fun j => x j i)

def totalComplexCoordinates (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) :
    TotalAmbient K ≃ₗ[ℂ] (Sum (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) → ℂ) :=
  (LinearEquiv.finTwoArrow ℂ (HeckeCycles.GeometricSource.CM.Ambient K)).trans <|
    ((C 0).complex.prodCongr (C 1).complex).trans <|
    (LinearEquiv.prodProdProdComm ℂ _ _ _ _).trans <|
    ((LinearEquiv.sumArrowLequivProdArrow (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ ℂ).symm.prodCongr
      (LinearEquiv.sumArrowLequivProdArrow (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ ℂ).symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) ℂ ℂ).symm

theorem total_complex_coordinates_embedding (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (x : TransportNew.CM.TensorPositions K) :
    totalComplexCoordinates K C (totalEmbedding K x) =
      fun i => (PeriodTotal.CM.totalSymplecticCoordinates K C x i : ℂ) := by
  funext i
  rcases i with i | i <;> rcases i with i | i
  · change ((C 0).complex (HeckeCycles.GeometricSource.CM.embeddingCoordinates K (fun j => x j 0))).1 i = _
    rw [(C 0).extends_rational]
    rfl
  · change ((C 1).complex (HeckeCycles.GeometricSource.CM.embeddingCoordinates K (fun j => x j 1))).1 i = _
    rw [(C 1).extends_rational]
    rfl
  · change ((C 0).complex (HeckeCycles.GeometricSource.CM.embeddingCoordinates K (fun j => x j 0))).2 i = _
    rw [(C 0).extends_rational]
    rfl
  · change ((C 1).complex (HeckeCycles.GeometricSource.CM.embeddingCoordinates K (fun j => x j 1))).2 i = _
    rw [(C 1).extends_rational]
    rfl

/-- Agreement on actual rational vectors determines a complex-linear map;
the supplied coordinate equivalences identify their scalar extension. -/
theorem linear_maps_eq_of_rational_coordinates
    {VQ VC I W : Type*} [AddCommGroup VQ] [Module ℚ VQ]
    [AddCommGroup VC] [Module ℂ VC] [Fintype I] [DecidableEq I]
    [AddCommGroup W] [Module ℂ W]
    (cq : VQ ≃ₗ[ℚ] (I → ℚ)) (cc : VC ≃ₗ[ℂ] (I → ℂ)) (emb : VQ → VC)
    (he : ∀ x, cc (emb x) = fun i => (cq x i : ℂ))
    (f g : VC →ₗ[ℂ] W) (h : ∀ x, f (emb x) = g (emb x)) : f = g := by
  have hf : f.comp cc.symm.toLinearMap = g.comp cc.symm.toLinearMap := by
    apply (Pi.basisFun ℂ I).ext
    intro i
    let x := cq.symm (Pi.single i 1)
    have hx : cc (emb x) = Pi.single i 1 := by
      rw [he]
      change (fun j => (cq (cq.symm (Pi.single i 1)) j : ℂ)) = _
      rw [LinearEquiv.apply_symm_apply]
      funext j
      simp only [Pi.single_apply]
      split_ifs <;> simp
    have hu : cc.symm (Pi.single i 1) = emb x := by
      apply cc.injective
      rw [LinearEquiv.apply_symm_apply, hx]
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hu]
    exact h x
  apply LinearMap.ext
  intro u
  have hu := LinearMap.congr_fun hf (cc u)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hu

def complexTensorBasisChange (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) :
    TotalAmbient K →ₗ[ℂ] TotalAmbient K where
  toFun x i τ j := ∑ k : Fin 2, (τ (b k i) : ℂ) * x k τ j
  map_add' x y := by
    ext i τ j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i τ j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring

omit [NumberField K] [NumberField.IsCMField K] in
theorem complex_tensor_basis_change_embedding
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) (x : TransportNew.CM.TensorPositions K) :
    complexTensorBasisChange K b (totalEmbedding K x) =
      totalEmbedding K (TransportNew.CM.tensorBasisChange K b x) := by
  funext i τ j
  change (∑ k : Fin 2, (τ (b k i) : ℂ) * (τ (x j k) : ℂ)) =
    (τ ((b.equivFun.symm (x j)) i) : ℂ)
  rw [b.equivFun_symm_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    IntermediateField.coe_sum, IntermediateField.coe_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The scalar extension of the rational matrix is exactly the change of
the actual complex coordinates induced by the same multiplicity basis. -/
theorem total_basis_matrix_realizes_complex
    (C D : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) (x : TotalAmbient K) :
    (PeriodTotal.CM.totalBasisMatrix K C D b).map (algebraMap ℚ ℂ) *ᵥ totalComplexCoordinates K D x =
      totalComplexCoordinates K C (complexTensorBasisChange K b x) := by
  let f := (Matrix.toLin' ((PeriodTotal.CM.totalBasisMatrix K C D b).map (algebraMap ℚ ℂ))).comp
    (totalComplexCoordinates K D).toLinearMap
  let g := (totalComplexCoordinates K C).toLinearMap.comp (complexTensorBasisChange K b)
  have hfg : f = g := by
    apply linear_maps_eq_of_rational_coordinates
      (PeriodTotal.CM.totalSymplecticCoordinates K D) (totalComplexCoordinates K D)
      (totalEmbedding K) (total_complex_coordinates_embedding K D)
    intro q
    change (PeriodTotal.CM.totalBasisMatrix K C D b).map (algebraMap ℚ ℂ) *ᵥ
      totalComplexCoordinates K D (totalEmbedding K q) =
        totalComplexCoordinates K C (complexTensorBasisChange K b (totalEmbedding K q))
    rw [total_complex_coordinates_embedding, complex_tensor_basis_change_embedding,
      total_complex_coordinates_embedding]
    exact PeriodTotal.CM.total_basis_matrix_baseChange K (algebraMap ℚ ℂ) C D b q
  exact LinearMap.congr_fun hfg x

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComplexTransition.CM
