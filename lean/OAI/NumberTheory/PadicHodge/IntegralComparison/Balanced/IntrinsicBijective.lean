import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.IntrinsicFrameAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.TotalQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.Bijective

/-! # Intrinsic Bijective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.IntrinsicBijective.IntrinsicComparison

noncomputable section

/-! A genuine section-total quasi-isomorphism makes the literal
augmentation-normalized comparison with original Ext bijective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z w
variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {κ : Type v} (F : κ → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ J U)
  {Y : Sheaf J (ModuleCat.{max u v} R)} (I : InjectiveResolution Y)
  (K : CochainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ) (g : K ⟶ I.cocomplex)

private instance moduleCoproducts (S : Type*) [CommRing S] : HasCoproducts.{0} (ModuleCat.{w} S) :=
  fun T => (ModuleCat.hasColimitsOfSize.{w, _, 0, 0} S).has_colimits_of_shape (Discrete T)

local instance coefficientProducts : HasProducts.{v} (ModuleCat.{max u v} R) :=
  fun T => (ModuleCat.hasLimitsOfSize.{v,v,max u v,max u v}).has_limits_of_shape (Discrete T)

local instance cechAdditive :
    (NonemptyCechNerve.complexFunctor F (A := ModuleCat.{max u v} R)).Additive := by
  dsimp only [NonemptyCechNerve.complexFunctor]
  infer_instance

def bicomplexMap : FrameCech.IntrinsicTotalCoordinates.Intrinsic.bicomplex.{u,v} F R J K ⟶
    FrameCech.IntrinsicTotalCoordinates.Intrinsic.bicomplex.{u,v} F R J I.cocomplex :=
  ((NonemptyCechNerve.complexFunctor F).mapHomologicalComplex (.up ℕ)).map
    (((sheafToPresheaf J (ModuleCat.{max u v} R)).mapHomologicalComplex (.up ℕ)).map g)

def totalMap := HomologicalComplex₂.total.map (bicomplexMap F R J I K g) (.up ℕ)

variable [hTotal : QuasiIso (totalMap F R J I K g)]

include hTotal in
theorem lifted_quasiIso : QuasiIso
    (FrameCech.AugmentationNaturality.totalMap.{u,v,z} F R J K I.cocomplex g) := by
  let : QuasiIso (HomologicalComplex₂.total.map (bicomplexMap F R J I K g) (.up ℕ)) := hTotal
  exact Mapped.TotalQuasiIso.quasiIso (ModuleCat.uliftFunctor.{z,max u v} R)
    (bicomplexMap F R J I K g)

include hTotal in
theorem bijective (i : ℕ) : Function.Bijective
    (IntrinsicFrameAugmentation.Intrinsic.comparison.{u,v,z} F R J hcover I K g i) := by
  let := lifted_quasiIso F R J I K g
  have hc : IsIso (FrameAugmentation.comparison.{u,v,z} F R J hcover I K g i) := by
    dsimp only [FrameAugmentation.comparison]
    infer_instance
  exact Lifted.Bijective.Comparison.bijective
    (FrameCech.IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,v,z} F R J K) i
    (FrameAugmentation.comparison.{u,v,z} F R J hcover I K g i).hom
    ((asIso (FrameAugmentation.comparison.{u,v,z} F R J hcover I K g i)).toLinearEquiv.bijective)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.IntrinsicBijective.IntrinsicComparison
