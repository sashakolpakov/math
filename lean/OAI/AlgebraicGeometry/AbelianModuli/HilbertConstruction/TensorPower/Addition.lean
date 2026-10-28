import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SumFrameTransport

/-! # Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Gluing the degree-addition isomorphism for actual line-bundle tensor powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def TensorPower.Addition.powerSumGluingData (L : Line.Bundles.LineBundle X) (m n : ℕ) :
    OpenPullback.MapGluing.OpenPullbackModuleMaps (LineBundle.EndGluing.lineEndFrameCover L) (TensorPower.PowerSheaf.tensorPowerModule L.sheaf (m + n))
      (Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L.sheaf m) (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n)) where
  localMap i := (Power.SumFrames.localPowerSumIso i.openSet.ι L i.frame m n).hom
  agree i j V hi hj := by
    let e := (L.frameRestrict hi i.frame.symm).symm
    exact (Power.SumFrameTransport.localPowerSumIso_open_refine L hi i.frame e m n).trans
      (Power.SumFrameTransport.localPowerSumIso_open_refine L hj j.frame e m n).symm

def TensorPower.Addition.powerSumGluingMap (L : Line.Bundles.LineBundle X) (m n : ℕ) :
    TensorPower.PowerSheaf.tensorPowerModule L.sheaf (m + n) ⟶
      Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L.sheaf m) (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n) :=
  (TensorPower.Addition.powerSumGluingData L m n).glue (LineBundle.EndGluing.lineEndFrameCover_covers L)

theorem TensorPower.Addition.powerSumGluingMap_pullback (L : Line.Bundles.LineBundle X) (m n : ℕ) (i : LineBundle.EndGluing.LineEndFrameOpen L) :
    (Scheme.Modules.pullback i.openSet.ι).map (TensorPower.Addition.powerSumGluingMap L m n) =
      (Power.SumFrames.localPowerSumIso i.openSet.ι L i.frame m n).hom :=
  (TensorPower.Addition.powerSumGluingData L m n).glue_pullback (LineBundle.EndGluing.lineEndFrameCover_covers L) i

instance TensorPower.Addition.powerSumGluingMap_isIso (L : Line.Bundles.LineBundle X) (m n : ℕ) : IsIso (TensorPower.Addition.powerSumGluingMap L m n) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨i, hi⟩ := LineBundle.EndGluing.lineEndFrameCover_covers L x
  refine ⟨i.openSet, hi, ?_⟩
  rw [TensorPower.Addition.powerSumGluingMap_pullback]
  infer_instance

def Line.Bundles.LineBundle.tensorPowerAddIso (L : Line.Bundles.LineBundle X) (m n : ℕ) :
    (L.tensorPower (m + n)).sheaf ≅ ((L.tensorPower m).tensor (L.tensorPower n)).sheaf := by
  let e : TensorPower.PowerSheaf.tensorPowerModule L.sheaf (m + n) ≅
      Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L.sheaf m) (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n) :=
    asIso (TensorPower.Addition.powerSumGluingMap L m n)
  exact e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
