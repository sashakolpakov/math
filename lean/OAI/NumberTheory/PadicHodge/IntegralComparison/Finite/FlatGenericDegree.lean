import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NormalAffineGenericRank
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree

/-! # Flat Generic Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatGenericDegree

noncomputable section

/-! The rank of a finite flat dominant map at the generic point is the
actual degree of its function-field extension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped TensorProduct

theorem finiteFlat_finrank_generic_eq_residueDegree
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [IsDominant f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    f.finrank (genericPoint Y) = f.residueDegree (genericPoint X) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := genericPoint Y) (U := (⊤ : Y.Opens)) (by trivial)
  have : Nonempty U := ⟨⟨genericPoint Y, hx⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint X, by
    change f (genericPoint X) ∈ U
    rw [AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension.dominant_genericPoint f]
    exact hx⟩⟩
  let := AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
  let := AlgebraicGeometry.SheafCohomology.Projective.FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
  have := ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionModule_finite f U hU
  have := ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionModule_flat f U hU
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  let q : PrimeSpectrum Y.functionField := ⟨⊥, inferInstance⟩
  have hq : q.comap (algebraMap Γ(Y, U) Y.functionField) = ⊥ := by
    apply PrimeSpectrum.ext
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      (IsFractionRing.injective Γ(Y, U) Y.functionField)
  have hr := Module.rankAtStalk_baseChange
    (R := Γ(Y, U)) (M := Γ(X, f ⁻¹ᵁ U)) q
  rw [Module.rankAtStalk_eq_finrank_of_free, hq] at hr
  change Module.finrank Y.functionField (Y.functionField ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U)) =
    Module.rankAtStalk (R := Γ(Y, U)) Γ(X, f ⁻¹ᵁ U) ⊥ at hr
  have he : hU.fromSpec (⊥ : PrimeSpectrum Γ(Y, U)) = genericPoint Y :=
    by simpa using genericPoint_eq_of_isOpenImmersion hU.fromSpec
  rw [← he, ← ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionModule_rank f U hU,
    ← hr, AlgebraicGeometry.SheafCohomology.Projective.NormalAffineGenericRank.Dimension.affinePreimageSectionModule_genericRank f hX U hU,
    AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree.Dimension.dominantFunctionField_finrank_eq_residueDegree f]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatGenericDegree
