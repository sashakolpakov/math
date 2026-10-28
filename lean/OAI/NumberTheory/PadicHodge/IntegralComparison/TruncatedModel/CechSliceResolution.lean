import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafSliceDiagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.EtaleSliceResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality

/-! # Cech Slice Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution

noncomputable section

/-! The canonical global native Čech augmentation is a quasi-isomorphism
on every frame slice of the actual finite integral coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

def opens (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) : X.left.affineOpens := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X i

local notation "W" => WittVector p k
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.diagram p k n X Y f hp
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.source p k n Y
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.cone p k n X Y f hp

variable (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X)

def restriction := Relative.ComplexRestriction.restriction (B := W)
  (Over.forget (Truncated.AffineModelFrame.frame p k n X Y f hp (U i).val (U i).property))

local instance restriction_additive : (restriction p k n X Y f hp i).Additive := by
  dsimp only [restriction]
  infer_instance

def localDiagram := GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped (restriction p k n X Y f hp i) P

def localCone := GeometricComparison.CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone (restriction p k n X Y f hp i) P M η

omit [X.left.IsSeparated] in
theorem localDiagram_eq : localDiagram p k n X Y f hp i =
    PresheafSliceDiagram.diagram p k n X Y f hp (U i) := rfl

theorem meet_isIso (V : X.left.affineOpens) :
    IsIso ((localDiagram p k n X Y f hp i).map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op) := by
  rw [localDiagram_eq]
  exact PresheafSliceDiagram.meet_isIso p k n X Y f hp (U i) V

omit [X.left.IsSeparated] in
theorem chart_quasiIso : QuasiIso ((localCone p k n X Y f hp i).app (op (U i))) := by
  change QuasiIso ((GeometricComparison.CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone (restriction p k n X Y f hp i) P M η).app (op (U i)))
  rw [GeometricComparison.CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app]
  exact EtaleSliceResolution.onSlice p k n X Y f hp (U i)
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.originalIndex (Truncated.Witt.Ring p k n) X i) le_rfl

theorem local_total_quasiIso : QuasiIso
    (GeometricComparison.CechCone.Total.CechConeTotal.augmentation U (localDiagram p k n X Y f hp i)
      (((restriction p k n X Y f hp i).mapHomologicalComplex (.up ℕ)).obj M)
      (localCone p k n X Y f hp i)) := by
  exact @GeometricComparison.Semilattice.LocalCechTotal.SemilatticeLocalCechTotal.quasiIso W inferInstance X.left.affineOpens inferInstance _ _ _ U i
    (localDiagram p k n X Y f hp i) (fun V => meet_isIso p k n X Y f hp i V)
    (((restriction p k n X Y f hp i).mapHomologicalComplex (.up ℕ)).obj M) (localCone p k n X Y f hp i)
    (chart_quasiIso p k n X Y f hp i)

theorem restricted_quasiIso : QuasiIso
    (((restriction p k n X Y f hp i).mapHomologicalComplex (.up ℕ)).map
      (CechPresheaf.augmentation p k n X Y f hp U)) := by
  apply (quasiIso_iff_comp_right _ (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (restriction p k n X Y f hp i) U P).hom).mp
  change QuasiIso (((restriction p k n X Y f hp i).mapHomologicalComplex (.up ℕ)).map
    (GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η) ≫
    (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (restriction p k n X Y f hp i) U P).hom)
  erw [GeometricComparison.CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation]
  exact local_total_quasiIso p k n X Y f hp i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution
