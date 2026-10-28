import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.RefinementExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionRefinement

/-! # Frame Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameRefinement

noncomputable section

/-! The native Čech refinement map agrees, in the original section
coordinates, with refinement of the genuine Ext source resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.RefinementExt

universe u v z

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι κ : Type v} (F : ι → C) (G : κ → C) (ρ : ι → κ) (α : ∀ i, F i ⟶ G (ρ i))
  (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  [EnoughInjectives (Sheaf J (ModuleCat.{max u v} R))]
  (H : Sheaf J (ModuleCat.{max u v} R))
  (I : InjectiveResolution H)

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

variable [QuasiIso (CoveringPresentationResolution.augmentation J R F)]
  [QuasiIso (CoveringPresentationResolution.augmentation J R G)]
  (hF : ∀ a q, Subsingleton (Abelian.Ext.{max u v z}
    ((CoveringPresentationResolution.complex J R F).X a) H (q + 1)))
  (hG : ∀ a q, Subsingleton (Abelian.Ext.{max u v z}
    ((CoveringPresentationResolution.complex J R G).X a) H (q + 1)))

theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (FrameCech.RefinementExt.liftedMap F G ρ α R J H) i ≫
      (HomologicalComplex.homologyMap (FrameCech.Ext.Comparison.comparison F R J H).inv i ≫
        (ResolutionCohomology.homologyIso R (CoveringPresentationResolution.complex J R F)
          (CoveringPresentationResolution.augmentation J R F) I hF i).hom) =
      HomologicalComplex.homologyMap (FrameCech.Ext.Comparison.comparison G R J H).inv i ≫
        (ResolutionCohomology.homologyIso R (CoveringPresentationResolution.complex J R G)
          (CoveringPresentationResolution.augmentation J R G) I hG i).hom := by
  have hc := InverseCoordinateHomology.homology
    (FrameCech.Ext.Comparison.comparison G R J H) (FrameCech.Ext.Comparison.comparison F R J H)
    (FrameCech.RefinementExt.resolutionMap F G ρ α R J H) (FrameCech.RefinementExt.liftedMap F G ρ α R J H) (FrameCech.RefinementExt.complexes F G ρ α R J H) i
  have he := ResolutionRefinement.homology R H
    (CoveringPresentationResolution.complex J R G) (CoveringPresentationResolution.complex J R F)
    (Presentation.FamilyRefinement.Family.map F G ρ α R J)
    (CoveringPresentationResolution.augmentation J R G)
    (CoveringPresentationResolution.augmentation J R F)
    (Presentation.FamilyRefinement.Family.augmentation F G ρ α R J) I hG hF i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫
      (ResolutionCohomology.homologyIso R (CoveringPresentationResolution.complex J R F)
        (CoveringPresentationResolution.augmentation J R F) I hF i).hom) hc).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun a => HomologicalComplex.homologyMap
          (FrameCech.Ext.Comparison.comparison G R J H).inv i ≫ a) he)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameRefinement
