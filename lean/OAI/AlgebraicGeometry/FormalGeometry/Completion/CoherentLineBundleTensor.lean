import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorCoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence

/-! # Coherent Line Bundle Tensor -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentLineBundleTensor.Construction

noncomputable section

/-! Coherent modules tensored with actual line bundles, with canonical dual cancellation. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

universe u

attribute [local instance] SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

def coherentLineBundleTensor {X : Scheme.{u}} (M : X.Modules) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : X.Modules :=
  M ⊗ L.sheaf

instance coherentLineBundleTensor_quasicoherent {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (coherentLineBundleTensor M L).IsQuasicoherent :=
  (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L).tensorObj_isQuasicoherent

instance coherentLineBundleTensor_finiteType {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (coherentLineBundleTensor M L).IsFiniteType :=
  (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L).tensorObj_isFiniteType

def coherentLineBundleTensor_cancelDualIso {X : Scheme.{u}}
    (M : X.Modules) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    coherentLineBundleTensor (coherentLineBundleTensor M L) (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L) ≅ M :=
  (α_ M L.sheaf (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L).sheaf) ≪≫
    (Iso.refl M ⊗ᵢ Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.evaluation L) ≪≫ ρ_ M

theorem coherentLineBundleTensor_isZero_iff {X : Scheme.{u}} (M : X.Modules) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    IsZero (coherentLineBundleTensor M L) ↔ IsZero M := by
  let E := SheafCohomology.Projective.InvertibleTensorEquivalence.invertibleRightTensorEquivalence L.sheaf (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)
  change IsZero (E.functor.obj M) ↔ IsZero M
  exact ⟨fun h => (E.inverse.map_isZero h).of_iso (E.unitIso.app M), fun h => E.functor.map_isZero h⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentLineBundleTensor.Construction
