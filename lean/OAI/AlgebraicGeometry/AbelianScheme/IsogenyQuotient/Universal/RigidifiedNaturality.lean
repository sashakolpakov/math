import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.RigidifiedLine
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedNaturality

/-! # Rigidified Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Universal normalized comparisons commute with arbitrary parameter
pullback and agree with the existing Noetherian comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A]
  (D : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions A)

theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalComparison_pullback {T U : Over S} (j : U ⟶ T) (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b)
    (h' : D.relativeValue (j ≫ a) = D.relativeValue (j ≫ b)) :
    D.pullbackComparison j a b (D.universalComparison hΓ a b h) =
      D.universalComparison hΓ (j ≫ a) (j ≫ b) h' :=
  D.universalComparison_unique hΓ (j ≫ a) (j ≫ b) h' _
    (D.pullbackComparison_normalized j a b _ (D.universalComparison_normalized hΓ a b h))

theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalComparison_eq_noetherian
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b) :
    D.universalComparison hΓ a b h = D.comparison a b h :=
  D.comparison_unique a b h _ (D.universalComparison_normalized hΓ a b h)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
