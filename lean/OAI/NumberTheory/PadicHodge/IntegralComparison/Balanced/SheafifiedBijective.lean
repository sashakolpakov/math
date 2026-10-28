import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedCone
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.SectionCompositeBijective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedCoordinates

/-! # Sheafified Bijective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedBijective.Comparison

noncomputable section

/-! Bijectivity of the literal balanced Ext comparison follows directly
from the canonical injective-section map of its source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u z

variable {C : Type u} [Category.{0} C] [HasBinaryProducts C]
  {ι : Type} [Finite ι] (F : ι → C) (R : Type u) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (hcover : ∀ V, CoveringObjectsSheafDetection.sieve F V ∈ J V)
  {Y : Sheaf J (ModuleCat.{u} R)} (I : InjectiveResolution Y)
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)
  (g : Sheafified.ConstantCochainCoordinates.sheafComplex R J P ⟶ I.cocomplex)
  (hsections : QuasiIso (SheafifiedCone.Comparison.sectionsMap.{u,z} R J I M P a g))

attribute [local instance] SheafifiedCone.Comparison.coproducts
  SheafifiedCone.Comparison.smallLimits SheafifiedCone.Comparison.smallProducts

local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates.sheafComplex R J P

include hsections in
theorem bijective (i : ℕ) : Function.Bijective
    ((Lifted.AugmentationTransport.comparison
      (FrameCech.IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,0,z} F R J K) i
      (FrameAugmentation.comparison F R J hcover I K g i).hom).comp
      (HomologicalComplex.homologyMap (Sheafified.ConstantCechMap.map F R J M P a) i).hom) := Lifted.SectionCompositeBijective.bijective
  (FrameCech.IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,0,z} F R J K)
  (SheafifiedCone.Comparison.liftedMap.{u,z} F R J M P a)
  (Sheafified.ConstantCechMap.map F R J M P a)
  (SheafifiedCoordinates.Comparison.square.{u,z} F R J M P a)
  (SheafifiedCone.Comparison.sectionsMap.{u,z} R J I M P a g)
  (fun j => ModuleCat.of R (Abelian.Ext.{max u z}
    (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) Y j))
  (InjectiveSectionCohomology.homologyIso R
    (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) I)
  (FrameAugmentation.comparison F R J hcover I K g)
  (SheafifiedCoordinates.Comparison.homology.{u,z} F R J hcover I M P a g)
  hsections i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedBijective.Comparison
