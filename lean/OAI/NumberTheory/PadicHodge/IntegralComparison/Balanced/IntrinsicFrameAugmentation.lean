import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.IntrinsicTotalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.AugmentationTransport

/-! # Intrinsic Frame Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.IntrinsicFrameAugmentation.Intrinsic

noncomputable section

/-! The balanced original Ext comparison in the literal native
presheaf Čech total coordinates, normalized by the actual augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z w

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {κ : Type v} (F : κ → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ J U)
  {Y : Sheaf J (ModuleCat.{max u v} R)} (I : InjectiveResolution Y)
  (hP : ∀ a q, Subsingleton (Abelian.Ext.{max u v z}
    ((CoveringPresentationResolution.complex J R F).X a) Y (q + 1)))
  (K : CochainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ)
  (a : (CochainComplex.single₀ _).obj Y ⟶ K)
  (g : K ⟶ I.cocomplex) (h : a ≫ g = I.ι)

private instance moduleCoproducts (S : Type*) [CommRing S] : HasCoproducts.{0} (ModuleCat.{w} S) :=
  fun T => (ModuleCat.hasColimitsOfSize.{w, _, 0, 0} S).has_colimits_of_shape (Discrete T)

def comparison (i : ℕ) := Lifted.AugmentationTransport.comparison
  (FrameCech.IntrinsicTotalCoordinates.Intrinsic.totalIso.{u, v, z} F R J K) i
  (FrameAugmentation.comparison.{u, v, z} F R J hcover I K g i).hom

include h in
abbrev augmentation (i : ℕ) := Lifted.AugmentationTransport.augmentation
  (FrameCech.IntrinsicTotalCoordinates.Intrinsic.totalIso.{u, v, z} F R J K)
  (FrameCech.ExtCoefficientEdge.edge.{u, v, z} F R J K a)
  (FrameCech.IntrinsicTotalCoordinates.Intrinsic.edge.{u, v} F R J K a)
  (FrameCech.IntrinsicTotalCoordinates.Intrinsic.edge_square.{u, v, z} F R J K a) i
  (FrameAugmentation.comparison.{u, v, z} F R J hcover I K g i).hom
  (FrameCechCohomology.homologyIso.{u, v, z} F R J hcover I hP i).hom.hom
  (fun x => congrArg (fun b => b x)
    (FrameAugmentation.augmentation_homology.{u, v, z} F R J hcover I hP K a g h i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.IntrinsicFrameAugmentation.Intrinsic
