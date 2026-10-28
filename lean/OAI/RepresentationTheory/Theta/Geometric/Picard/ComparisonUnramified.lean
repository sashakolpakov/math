import OAI.RepresentationTheory.Theta.Geometric.Picard.ParameterComparison
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Comparison Unramified -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonUnramified

noncomputable section

/-! Separation on all test schemes removes relative infinitesimal
ambiguity from the actual Picard comparison projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {A N T : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian (N ⊗ T).left]
    (Q : OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A N) (L : OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A T)

theorem picardParameterProjection_formallyUnramified
    (hQ : ∀ U : Over (Spec (.of K)), Function.Injective (Q.relativeValue (T := U))) :
    FormallyUnramified (ParameterComparison.picardParameterProjection Q L).left := by
  have : Mono (ParameterComparison.picardParameterProjection Q L) := ParameterComparison.picardParameterProjection_mono Q L hQ
  have : Mono (ParameterComparison.picardParameterProjection Q L).left := Over.mono_left_of_mono _
  infer_instance

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonUnramified
