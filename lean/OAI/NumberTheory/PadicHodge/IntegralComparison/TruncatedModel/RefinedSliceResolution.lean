import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafSliceDiagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.EtaleSliceResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality

/-! # Refined Slice Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.RefinedSliceResolution

noncomputable section

/-! Every finite family of affine coordinate subcharts gives the original Cech resolution on each frame slice. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  {ι : Type} [Finite ι] (U : ι → X.left.affineOpens)
  (index : ι → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hU : ∀ i, (U i).val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X (index i)).val)

local notation "W" => WittVector p k
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.diagram p k n X Y f hp
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.source p k n Y
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.cone p k n X Y f hp

variable (i : ι)

def restriction := Relative.ComplexRestriction.restriction (B := W)
  (Over.forget (Truncated.AffineModelFrame.frame p k n X Y f hp (U i).val (U i).property))

local instance restriction_additive : (restriction p k n X Y f hp U i).Additive := by
  dsimp only [restriction]
  infer_instance

def localDiagram := GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped (restriction p k n X Y f hp U i) P

def localCone := GeometricComparison.CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone (restriction p k n X Y f hp U i) P M η

omit [X.left.IsSeparated] [IsProper X.hom] [Finite ι] in
theorem localDiagram_eq : localDiagram p k n X Y f hp U i =
    PresheafSliceDiagram.diagram p k n X Y f hp (U i) := rfl

omit [IsProper X.hom] [Finite ι] in
theorem meet_isIso (V : X.left.affineOpens) :
    IsIso ((localDiagram p k n X Y f hp U i).map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op) := by
  rw [localDiagram_eq]
  exact PresheafSliceDiagram.meet_isIso p k n X Y f hp (U i) V

include hU in
omit [X.left.IsSeparated] [Finite ι] in
theorem chart_quasiIso : QuasiIso ((localCone p k n X Y f hp U i).app (op (U i))) := by
  change QuasiIso ((GeometricComparison.CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone (restriction p k n X Y f hp U i) P M η).app (op (U i)))
  rw [GeometricComparison.CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app]
  exact EtaleSliceResolution.onSlice p k n X Y f hp (U i)
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.originalIndex (Truncated.Witt.Ring p k n) X (index i)) (hU i)

include hU in
omit [Finite ι] in
theorem local_total_quasiIso : QuasiIso
    (GeometricComparison.CechCone.Total.CechConeTotal.augmentation U (localDiagram p k n X Y f hp U i)
      (((restriction p k n X Y f hp U i).mapHomologicalComplex (.up ℕ)).obj M)
      (localCone p k n X Y f hp U i)) := by
  exact @GeometricComparison.Semilattice.LocalCechTotal.SemilatticeLocalCechTotal.quasiIso W inferInstance X.left.affineOpens inferInstance _ _ _ U i
    (localDiagram p k n X Y f hp U i) (fun V => meet_isIso p k n X Y f hp U i V)
    (((restriction p k n X Y f hp U i).mapHomologicalComplex (.up ℕ)).obj M) (localCone p k n X Y f hp U i)
    (chart_quasiIso p k n X Y f hp U index hU i)

include hU in
theorem restricted_quasiIso : QuasiIso
    (((restriction p k n X Y f hp U i).mapHomologicalComplex (.up ℕ)).map
      (CechPresheaf.augmentation p k n X Y f hp U)) := by
  apply (quasiIso_iff_comp_right _ (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (restriction p k n X Y f hp U i) U P).hom).mp
  change QuasiIso (((restriction p k n X Y f hp U i).mapHomologicalComplex (.up ℕ)).map
    (GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η) ≫
    (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (restriction p k n X Y f hp U i) U P).hom)
  erw [GeometricComparison.CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation]
  exact local_total_quasiIso p k n X Y f hp U index hU i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.RefinedSliceResolution
