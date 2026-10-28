import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FactorizationParameter

/-! # Universal Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.UniversalFactorization

noncomputable section

/-! The closed factorization parameter carries its actual universal factorization, with exact compatibility with the given embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P Z : Over M.left}
variable [IsProper X.hom] [Flat X.hom] (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P)

theorem properFactorizationParameter_universal_existsUnique :
    ∃! h : (Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj X ⟶
        (Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj Z,
      h ≫ (Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j =
        (Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map i := by
  apply (FactorizationIdeal.properFactorizationIdeal_test j i (FactorizationParameter.properFactorizationParameterInclusion M j i).left).mp
  change (FactorizationIdeal.properFactorizationIdeal j i).comap (FactorizationIdeal.properFactorizationIdeal j i).subschemeι = ⊥
  rw [Closed.ConditionIdeals.ideal_comap_eq_bot_iff, Scheme.IdealSheafData.ker_subschemeι]

def properUniversalFactorization :
    (Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj X ⟶
      (Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj Z :=
  (properFactorizationParameter_universal_existsUnique M j i).choose

theorem properUniversalFactorization_fac :
    properUniversalFactorization M j i ≫
      (Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j =
        (Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map i :=
  (properFactorizationParameter_universal_existsUnique M j i).choose_spec.1

theorem properUniversalFactorization_closed [IsClosedImmersion i.left] :
    IsClosedImmersion (properUniversalFactorization M j i).left := by
  have : IsClosedImmersion
      ((Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j).left :=
    Projective.PresentationBaseChange.overPullback_map_closed j _
  have : IsClosedImmersion
      ((Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map i).left :=
    Projective.PresentationBaseChange.overPullback_map_closed i _
  have he := congrArg Over.Hom.left (properUniversalFactorization_fac M j i)
  change (properUniversalFactorization M j i).left ≫
      ((Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j).left =
        ((Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map i).left at he
  have : IsClosedImmersion ((properUniversalFactorization M j i).left ≫
      ((Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j).left) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp (properUniversalFactorization M j i).left
    ((Over.pullback (FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j).left

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.UniversalFactorization
