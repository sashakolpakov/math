import OAI.RepresentationTheory.Theta.Geometric.Picard.ParameterComparison

/-! # Comparison Parameter -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonParameter

noncomputable section

/-! An isomorphic actual comparison projection recovers the unique
parameter map and the original relative Picard class of the family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {A N T : Over (Spec (.of K))}
    [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian (N ⊗ T).left]
    (Q : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A N) (L : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A T)

theorem exists_picard_parameter_of_comparison_isIso
    [IsIso (ParameterComparison.picardParameterProjection Q L).left] :
    ∃ a : T ⟶ N, Q.relativeValue a = L.relativeValue (𝟙 T) := by
  have : IsIso ((Over.forget (Spec (.of K))).map (ParameterComparison.picardParameterProjection Q L)) :=
    inferInstanceAs (IsIso (ParameterComparison.picardParameterProjection Q L).left)
  have : IsIso (ParameterComparison.picardParameterProjection Q L) :=
    isIso_of_reflects_iso (ParameterComparison.picardParameterProjection Q L) (Over.forget (Spec (.of K)))
  refine ⟨inv (ParameterComparison.picardParameterProjection Q L) ≫ ParameterComparison.picardParameterMap Q L, ?_⟩
  have h := ParameterComparison.picardParameterComparison_value Q L (inv (ParameterComparison.picardParameterProjection Q L))
  rwa [IsIso.inv_hom_id] at h

theorem existsUnique_picard_parameter_of_comparison_isIso
    [IsIso (ParameterComparison.picardParameterProjection Q L).left]
    (hQ : Function.Injective (Q.relativeValue (T := T))) :
    ∃! a : T ⟶ N, Q.relativeValue a = L.relativeValue (𝟙 T) := by
  obtain ⟨a, ha⟩ := exists_picard_parameter_of_comparison_isIso Q L
  exact ⟨a, ha, fun b hb => hQ (hb.trans ha.symm)⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonParameter
