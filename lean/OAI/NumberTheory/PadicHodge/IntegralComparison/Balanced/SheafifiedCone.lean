import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameSourcePrecomposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCechMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.IntrinsicFrameAugmentation

/-! # Sheafified Cone -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedCone.Comparison

noncomputable section

/-! The balanced comparison of a genuine sheafified constant-complex
cone is exactly its original injective-section cohomology map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

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

local instance coproducts : HasCoproducts.{0} (ModuleCat.{max u z} R) :=
  fun T => (ModuleCat.hasColimitsOfSize.{max u z,u,0,0} R).has_colimits_of_shape (Discrete T)
local instance smallLimits : HasLimitsOfSize.{0,0} (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfSize.{0,0,u,u}
local instance smallProducts : HasProducts.{0} (ModuleCat.{u} R) :=
  fun T => (smallLimits (R := R)).has_limits_of_shape (Discrete T)

local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates.sheafComplex R J P
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates.sectionMap R J M P a
local notation "c" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameAugmentation.comparison F R J hcover I K g

def liftedMap := s ≫ FrameSourceNormalization.edge F R J K

def sectionsMap := s ≫ ResolutionHom.SourceNaturality.sectionsMap R g

def sectionComparison (i : ℕ) :=
  HomologicalComplex.homologyMap (sectionsMap R J I M P a g) i ≫
    (InjectiveSectionCohomology.homologyIso R (Ext.ZeroPresheafSections.constantUnit R J) I i).hom

theorem square : liftedMap F R J M P a ≫
    (FrameCech.IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,0,z} F R J K).hom =
      ((ModuleCat.uliftFunctor.{z,u} R).mapHomologicalComplex (.up ℕ)).map
        (Sheafified.ConstantCechMap.map F R J M P a) := FrameSourcePrecomposition.square F R J K
  (ConstantSection.ComplexMap.source R M) s
  (((ModuleCat.uliftFunctor.{z,u} R).mapHomologicalComplex (.up ℕ)).map
    (Sheafified.ConstantCechMap.map F R J M P a))
  (Sheafified.ConstantCechMap.square.{u,z} F R J M P a)

omit [Finite ι] in
theorem lifted_homology (i : ℕ) :
    HomologicalComplex.homologyMap (liftedMap F R J M P a) i ≫ c i =
      sectionComparison R J I M P a g i := FrameSourcePrecomposition.homology
  F R J K (ConstantSection.ComplexMap.source R M) s hcover I g i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedCone.Comparison
