import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenIsomorphismGluing

/-! # Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The power of a tensor product of line bundles is isomorphic to the tensor product of their powers, by gluing the checked local comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

structure TensorPower.Gluing.TensorFrameOpen (L M : Line.Bundles.LineBundle X) where
  openSet : X.Opens
  leftFrame : Line.Bundles.structureModule openSet.toScheme ≅ (Scheme.Modules.pullback openSet.ι).obj L.sheaf
  rightFrame : Line.Bundles.structureModule openSet.toScheme ≅ (Scheme.Modules.pullback openSet.ι).obj M.sheaf

def TensorPower.Gluing.tensorFrameCover (L M : Line.Bundles.LineBundle X) : TensorPower.Gluing.TensorFrameOpen L M → X.Opens := TensorPower.Gluing.TensorFrameOpen.openSet

theorem TensorPower.Gluing.tensorFrameCover_covers (L M : Line.Bundles.LineBundle X) (x : X) :
    ∃ i : TensorPower.Gluing.TensorFrameOpen L M, x ∈ TensorPower.Gluing.tensorFrameCover L M i := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial x
  obtain ⟨V, hxV, ⟨f⟩⟩ := M.locallyTrivial x
  exact ⟨⟨U ⊓ V, (L.frameRestrict inf_le_left e).symm, (M.frameRestrict inf_le_right f).symm⟩,
    hxU, hxV⟩

def TensorPower.Gluing.tensorPowerComparisonData (L M : Line.Bundles.LineBundle X) (n : ℕ) :
    Module.OpenMapGluing.OpenCoverModuleMaps (TensorPower.Gluing.tensorFrameCover L M)
      (TensorPower.PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L.sheaf M.sheaf) n)
      (Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n) (TensorPower.PowerSheaf.tensorPowerModule M.sheaf n)) where
  localMap i := (Local.TensorPowerComparison.localTensorPowerRestrictionIso i.openSet.ι i.leftFrame.hom i.rightFrame.hom n).hom
  agree i j V hi hj := by
    change V ≤ i.openSet at hi
    change V ≤ j.openSet at hj
    let f : V.toScheme ⟶ i.openSet.toScheme := X.homOfLE hi
    let g : V.toScheme ⟶ j.openSet.toScheme := X.homOfLE hj
    have : IsOpenImmersion f := inferInstanceAs (IsOpenImmersion (X.homOfLE hi))
    have : IsOpenImmersion g := inferInstanceAs (IsOpenImmersion (X.homOfLE hj))
    have hfi : f ≫ i.openSet.ι = V.ι := X.homOfLE_ι hi
    have hgj : g ≫ j.openSet.ι = V.ι := X.homOfLE_ι hj
    have hiV : V ≤ (f ≫ i.openSet.ι).opensRange := by
      intro x hx
      change ∃ y : V.toScheme, (f ≫ i.openSet.ι) y = x
      exact ⟨⟨x, hx⟩, congrArg (fun k : V.toScheme ⟶ X => k ⟨x, hx⟩) hfi⟩
    have hjV : V ≤ (g ≫ j.openSet.ι).opensRange := by
      intro x hx
      change ∃ y : V.toScheme, (g ≫ j.openSet.ι) y = x
      exact ⟨⟨x, hx⟩, congrArg (fun k : V.toScheme ⟶ X => k ⟨x, hx⟩) hgj⟩
    have hiR : V ≤ i.openSet.ι.opensRange := by rwa [i.openSet.opensRange_ι]
    have hjR : V ≤ j.openSet.ι.opensRange := by rwa [j.openSet.opensRange_ι]
    have H : Local.TensorPowerValues.localTensorPowerValue i.openSet.ι i.leftFrame i.rightFrame n V hiR =
        Local.TensorPowerValues.localTensorPowerValue j.openSet.ι j.leftFrame j.rightFrame n V hjR :=
      (Local.TensorPowerValues.localTensorPowerValue_comp f i.openSet.ι i.leftFrame i.rightFrame n V hiV).symm.trans
      ((Local.TensorPowerValues.localTensorPowerValue_congr (hfi.trans hgj.symm)
        (Local.TensorPowerValues.refinedPullbackFrame f i.openSet.ι i.leftFrame) (Local.TensorPowerValues.refinedPullbackFrame g j.openSet.ι j.leftFrame)
        (Local.TensorPowerValues.refinedPullbackFrame f i.openSet.ι i.rightFrame) (Local.TensorPowerValues.refinedPullbackFrame g j.openSet.ι j.rightFrame)
        n V hiV hjV).trans
          (Local.TensorPowerValues.localTensorPowerValue_comp g j.openSet.ι j.leftFrame j.rightFrame n V hjV))
    exact (Local.TensorPowerValues.localTensorPowerValue_restriction i.openSet.ι i.leftFrame i.rightFrame n V hiR).trans
      (H.trans (Local.TensorPowerValues.localTensorPowerValue_restriction j.openSet.ι j.leftFrame j.rightFrame n V hjR).symm)

def Line.Bundles.LineBundle.tensorPowerTensorIso (L M : Line.Bundles.LineBundle X) (n : ℕ) :
    ((L.tensor M).tensorPower n).sheaf ≅ ((L.tensorPower n).tensor (M.tensorPower n)).sheaf :=
  (TensorPower.Gluing.tensorPowerComparisonData L M n).glueIso (TensorPower.Gluing.tensorFrameCover_covers L M)
    (fun i => inferInstanceAs (IsIso
      (Local.TensorPowerComparison.localTensorPowerRestrictionIso i.openSet.ι i.leftFrame.hom i.rightFrame.hom n).hom))

theorem Line.Bundles.LineBundle.tensorPowerTensorIso_restrict (L M : Line.Bundles.LineBundle X) (n : ℕ) (i : TensorPower.Gluing.TensorFrameOpen L M) :
    (Scheme.Modules.restrictFunctor i.openSet.ι).map (L.tensorPowerTensorIso M n).hom =
      (Local.TensorPowerComparison.localTensorPowerRestrictionIso i.openSet.ι i.leftFrame.hom i.rightFrame.hom n).hom :=
  (TensorPower.Gluing.tensorPowerComparisonData L M n).glueIso_restrict (TensorPower.Gluing.tensorFrameCover_covers L M) _ i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
