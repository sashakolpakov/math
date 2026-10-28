import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PresheafSliceDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SubchartSliceResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality

/-! # Refined Cech Slice Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedCechSliceResolution.IntrinsicPadicRefinedCechSliceResolution

noncomputable section

/-! A finite family of affine coordinate subcharts gives the original
Cech resolution on each of its frame slices. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) {ι : Type} [Finite ι] (U : ι → X.left.affineOpens)
  (index : ι → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hU : ∀ i, (U i).val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X (index i))

local notation "W" => WittVector p (ZMod p)
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.source p Y n
local notation "η" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.cone p X Y f hp n

variable (i : ι)

def restriction := IntegralComparison.Relative.ComplexRestriction.restriction (B := W)
  (Over.forget (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (U i).val (U i).property n))

local instance restriction_additive : (restriction p X Y f hp n U i).Additive := by
  dsimp only [restriction]
  infer_instance

def localDiagram := CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped (restriction p X Y f hp n U i) P
def localCone := CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone (restriction p X Y f hp n U i) P M η

omit [X.left.IsSeparated] [IsProper X.hom] [Finite ι] in
theorem localDiagram_eq : localDiagram p X Y f hp n U i =
    PresheafSliceDiagram.IntrinsicPadicPresheafSliceDiagram.diagram p X Y f hp n (U i) := rfl

omit [IsProper X.hom] [Finite ι] in
theorem meet_isIso (V : X.left.affineOpens) :
    IsIso ((localDiagram p X Y f hp n U i).map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op) := by
  rw [localDiagram_eq]
  exact PresheafSliceDiagram.IntrinsicPadicPresheafSliceDiagram.meet_isIso p X Y f hp n (U i) V

include hU in
omit [X.left.IsSeparated] [Finite ι] in
theorem chart_quasiIso : QuasiIso ((localCone p X Y f hp n U i).app (op (U i))) := by
  change QuasiIso ((CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone (restriction p X Y f hp n U i) P M η).app (op (U i)))
  rw [CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app]
  exact SubchartSliceResolution.IntrinsicPadicSubchartSliceResolution.onSlice p X Y f hp n (U i) (index i) (hU i)

include hU in
omit [Finite ι] in
theorem local_total_quasiIso : QuasiIso
    (CechCone.Total.CechConeTotal.augmentation U (localDiagram p X Y f hp n U i)
      (((restriction p X Y f hp n U i).mapHomologicalComplex (.up ℕ)).obj M)
      (localCone p X Y f hp n U i)) := by
  exact @Semilattice.LocalCechTotal.SemilatticeLocalCechTotal.quasiIso W inferInstance X.left.affineOpens inferInstance _ _ _ U i
    (localDiagram p X Y f hp n U i) (fun V => meet_isIso p X Y f hp n U i V)
    (((restriction p X Y f hp n U i).mapHomologicalComplex (.up ℕ)).obj M) (localCone p X Y f hp n U i)
    (chart_quasiIso p X Y f hp n U index hU i)

include hU in
theorem restricted_quasiIso : QuasiIso
    (((restriction p X Y f hp n U i).mapHomologicalComplex (.up ℕ)).map
      (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U)) := by
  apply (quasiIso_iff_comp_right _ (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (restriction p X Y f hp n U i) U P).hom).mp
  change QuasiIso (((restriction p X Y f hp n U i).mapHomologicalComplex (.up ℕ)).map
    (CechCone.Total.CechConeTotal.augmentation U P M η) ≫
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (restriction p X Y f hp n U i) U P).hom)
  erw [CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation]
  exact local_total_quasiIso p X Y f hp n U index hU i

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedCechSliceResolution.IntrinsicPadicRefinedCechSliceResolution
