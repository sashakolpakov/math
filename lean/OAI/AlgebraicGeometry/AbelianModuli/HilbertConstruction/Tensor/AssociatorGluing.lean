import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorAssociatorValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenIsomorphismGluing

/-! # Associator Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Associativity of tensor products of line bundles, constructed by gluing frame-independent local isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

structure Tensor.AssociatorGluing.TripleTensorFrameOpen (L M N : Line.Bundles.LineBundle X) where
  openSet : X.Opens
  leftFrame : Line.Bundles.structureModule openSet.toScheme ≅ (Scheme.Modules.pullback openSet.ι).obj L.sheaf
  middleFrame : Line.Bundles.structureModule openSet.toScheme ≅ (Scheme.Modules.pullback openSet.ι).obj M.sheaf
  rightFrame : Line.Bundles.structureModule openSet.toScheme ≅ (Scheme.Modules.pullback openSet.ι).obj N.sheaf

def Tensor.AssociatorGluing.tripleTensorFrameCover (L M N : Line.Bundles.LineBundle X) : Tensor.AssociatorGluing.TripleTensorFrameOpen L M N → X.Opens :=
  Tensor.AssociatorGluing.TripleTensorFrameOpen.openSet

theorem Tensor.AssociatorGluing.tripleTensorFrameCover_covers (L M N : Line.Bundles.LineBundle X) (x : X) :
    ∃ i : Tensor.AssociatorGluing.TripleTensorFrameOpen L M N, x ∈ Tensor.AssociatorGluing.tripleTensorFrameCover L M N i := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial x
  obtain ⟨V, hxV, ⟨f⟩⟩ := M.locallyTrivial x
  obtain ⟨W, hxW, ⟨g⟩⟩ := N.locallyTrivial x
  exact ⟨⟨(U ⊓ V) ⊓ W, (L.frameRestrict (inf_le_left.trans inf_le_left) e).symm,
    (M.frameRestrict (inf_le_left.trans inf_le_right) f).symm,
    (N.frameRestrict inf_le_right g).symm⟩, ⟨hxU, hxV⟩, hxW⟩

def Tensor.AssociatorGluing.tensorAssociatorData (L M N : Line.Bundles.LineBundle X) :
    Module.OpenMapGluing.OpenCoverModuleMaps (Tensor.AssociatorGluing.tripleTensorFrameCover L M N)
      (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule L.sheaf M.sheaf) N.sheaf)
      (Tensor.ProductSheaf.tensorModule L.sheaf (Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf)) where
  localMap i := (Local.TensorAssociator.localTensorAssociatorRestrictionIso i.openSet.ι
    i.leftFrame.hom i.middleFrame.hom i.rightFrame.hom).hom
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
    have H : Local.TensorAssociatorValues.localTensorAssociatorValue i.openSet.ι i.leftFrame i.middleFrame i.rightFrame V hiR =
        Local.TensorAssociatorValues.localTensorAssociatorValue j.openSet.ι j.leftFrame j.middleFrame j.rightFrame V hjR :=
      (Local.TensorAssociatorValues.localTensorAssociatorValue_comp f i.openSet.ι i.leftFrame i.middleFrame i.rightFrame V hiV).symm.trans
      ((Local.TensorAssociatorValues.localTensorAssociatorValue_congr (hfi.trans hgj.symm)
        (Local.TensorPowerValues.refinedPullbackFrame f i.openSet.ι i.leftFrame) (Local.TensorPowerValues.refinedPullbackFrame g j.openSet.ι j.leftFrame)
        (Local.TensorPowerValues.refinedPullbackFrame f i.openSet.ι i.middleFrame) (Local.TensorPowerValues.refinedPullbackFrame g j.openSet.ι j.middleFrame)
        (Local.TensorPowerValues.refinedPullbackFrame f i.openSet.ι i.rightFrame) (Local.TensorPowerValues.refinedPullbackFrame g j.openSet.ι j.rightFrame)
        V hiV hjV).trans
          (Local.TensorAssociatorValues.localTensorAssociatorValue_comp g j.openSet.ι j.leftFrame j.middleFrame j.rightFrame V hjV))
    exact (Local.TensorAssociatorValues.localTensorAssociatorValue_restriction i.openSet.ι i.leftFrame i.middleFrame i.rightFrame V hiR).trans
      (H.trans (Local.TensorAssociatorValues.localTensorAssociatorValue_restriction j.openSet.ι j.leftFrame j.middleFrame j.rightFrame V hjR).symm)

def Line.Bundles.LineBundle.tensorAssocIso (L M N : Line.Bundles.LineBundle X) :
    ((L.tensor M).tensor N).sheaf ≅ (L.tensor (M.tensor N)).sheaf :=
  (Tensor.AssociatorGluing.tensorAssociatorData L M N).glueIso (Tensor.AssociatorGluing.tripleTensorFrameCover_covers L M N)
    (fun i => inferInstanceAs (IsIso (Local.TensorAssociator.localTensorAssociatorRestrictionIso i.openSet.ι
      i.leftFrame.hom i.middleFrame.hom i.rightFrame.hom).hom))

theorem Line.Bundles.LineBundle.tensorAssocIso_restrict (L M N : Line.Bundles.LineBundle X) (i : Tensor.AssociatorGluing.TripleTensorFrameOpen L M N) :
    (Scheme.Modules.restrictFunctor i.openSet.ι).map (L.tensorAssocIso M N).hom =
      (Local.TensorAssociator.localTensorAssociatorRestrictionIso i.openSet.ι
        i.leftFrame.hom i.middleFrame.hom i.rightFrame.hom).hom :=
  (Tensor.AssociatorGluing.tensorAssociatorData L M N).glueIso_restrict (Tensor.AssociatorGluing.tripleTensorFrameCover_covers L M N) _ i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
