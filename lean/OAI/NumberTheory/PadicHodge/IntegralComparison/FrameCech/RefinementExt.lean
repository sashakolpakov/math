import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.FamilyRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyRefinementCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Refinement Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.RefinementExt

noncomputable section

/-! The native Čech refinement map agrees, in the original section
coordinates, with refinement of the genuine Ext source resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v z

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι κ : Type v} (F : ι → C) (G : κ → C) (ρ : ι → κ) (α : ∀ i, F i ⟶ G (ρ i))
  (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (H : Sheaf J (ModuleCat.{max u v} R))

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

def cochainMap : Differential.complex G R H.obj ⟶
    Differential.complex F R H.obj :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).map
    (Cech.FamilyRefinement.Family.map F G ρ α H.obj)

omit [HasExt (Sheaf J (ModuleCat R))] in
theorem cochainMap_coordinate (n : ℕ) (t : Fin (n + 1) → ι) :
    (cochainMap F G ρ α R J H).f n ≫ Differential.coordinate F R H.obj n t =
      Differential.coordinate G R H.obj n (ρ ∘ t) ≫
        H.obj.map (Frame.TupleRefinement.map (𝟭 C) F G ρ α n t).op := Pi.lift_comp_π _ t

def liftedMap : FrameCech.Ext.Comparison.liftedComplex.{u, v, z} G R J H ⟶
    FrameCech.Ext.Comparison.liftedComplex.{u, v, z} F R J H :=
  ((ModuleCat.uliftFunctor.{z, max u v} R).mapHomologicalComplex (.up ℕ)).map
    (cochainMap F G ρ α R J H)

def resolutionMap := Acyclic.ChainRefinement.map R H
  (CoveringPresentationResolution.complex J R G) (CoveringPresentationResolution.complex J R F)
    (Presentation.FamilyRefinement.Family.map F G ρ α R J)

omit [HasBinaryProducts C] in
theorem resolutionMap_mk (n : ℕ) (f : (CoveringPresentationResolution.complex J R G).X n ⟶ H) :
    (resolutionMap F G ρ α R J H).f n (Abelian.Ext.mk₀ f) =
      Abelian.Ext.mk₀ ((Presentation.FamilyRefinement.Family.map F G ρ α R J).f n ≫ f) :=
  Abelian.Ext.mk₀_comp_mk₀ _ _

theorem coordinate (n : ℕ) (t : Fin (n + 1) → ι)
    (f : (CoveringPresentationResolution.complex J R G).X n ⟶ H) :
    Differential.coordinate F R H.obj n t
      (((FrameCech.Ext.Comparison.comparison F R J H).hom.f n
        ((resolutionMap F G ρ α R J H).f n (Abelian.Ext.mk₀ f))).down) =
      Differential.coordinate F R H.obj n t
        (((liftedMap F G ρ α R J H).f n
          ((FrameCech.Ext.Comparison.comparison G R J H).hom.f n (Abelian.Ext.mk₀ f))).down) := by
  have hl := (congrArg (fun x => Differential.coordinate F R H.obj n t
    (((FrameCech.Ext.Comparison.comparison F R J H).hom.f n x).down))
      (resolutionMap_mk F G ρ α R J H n f)).trans
        ((ExtCoordinates.coordinate_mk F R J H n t
          ((Presentation.FamilyRefinement.Family.map F G ρ α R J).f n ≫ f)).trans
            (Presentation.FamilyRefinementCoordinates.Family.sheaf F G ρ α n t R J H f))
  have hr := (congrArg (fun a => a
    (((FrameCech.Ext.Comparison.comparison G R J H).hom.f n (Abelian.Ext.mk₀ f)).down))
      (cochainMap_coordinate F G ρ α R J H n t)).trans
        (congrArg (H.obj.map (Frame.TupleRefinement.map (𝟭 C) F G ρ α n t).op)
          (ExtCoordinates.coordinate_mk G R J H n (ρ ∘ t) f))
  exact hl.trans hr.symm

theorem complexes : resolutionMap F G ρ α R J H ≫ (FrameCech.Ext.Comparison.comparison F R J H).hom =
    (FrameCech.Ext.Comparison.comparison G R J H).hom ≫ liftedMap F G ρ α R J H := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Abelian.Ext.{max u v z} ((CoveringPresentationResolution.complex J R G).X n) H 0 at x
  obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
  apply ULift.ext
  apply Module.ProductScalarKernel.element_ext
    (fun t => H.obj.obj (op (Presentation.TupleProducts.family F n t)))
  intro t
  exact coordinate F G ρ α R J H n t f

variable [QuasiIso (CoveringPresentationResolution.augmentation J R F)]
  [QuasiIso (CoveringPresentationResolution.augmentation J R G)]
  (hF : ∀ a q, Subsingleton (Abelian.Ext.{max u v z}
    ((CoveringPresentationResolution.complex J R F).X a) H (q + 1)))
  (hG : ∀ a q, Subsingleton (Abelian.Ext.{max u v z}
    ((CoveringPresentationResolution.complex J R G).X a) H (q + 1)))

theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (liftedMap F G ρ α R J H) i ≫
      (HomologicalComplex.homologyMap (FrameCech.Ext.Comparison.comparison F R J H).inv i ≫
        (Acyclic.ChainCohomology.homologyIso R H (CoveringPresentationResolution.complex J R F)
          (CoveringPresentationResolution.augmentation J R F) hF i).hom) =
      HomologicalComplex.homologyMap (FrameCech.Ext.Comparison.comparison G R J H).inv i ≫
        (Acyclic.ChainCohomology.homologyIso R H (CoveringPresentationResolution.complex J R G)
          (CoveringPresentationResolution.augmentation J R G) hG i).hom := by
  have hc := InverseCoordinateHomology.homology
    (FrameCech.Ext.Comparison.comparison G R J H) (FrameCech.Ext.Comparison.comparison F R J H)
    (resolutionMap F G ρ α R J H) (liftedMap F G ρ α R J H) (complexes F G ρ α R J H) i
  have he := Acyclic.ChainRefinement.homology R H
    (CoveringPresentationResolution.complex J R G) (CoveringPresentationResolution.complex J R F)
    (Presentation.FamilyRefinement.Family.map F G ρ α R J)
    (CoveringPresentationResolution.augmentation J R G)
    (CoveringPresentationResolution.augmentation J R F)
    (Presentation.FamilyRefinement.Family.augmentation F G ρ α R J) hG hF i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫
      (Acyclic.ChainCohomology.homologyIso R H (CoveringPresentationResolution.complex J R F)
        (CoveringPresentationResolution.augmentation J R F) hF i).hom) hc).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun a => HomologicalComplex.homologyMap
          (FrameCech.Ext.Comparison.comparison G R J H).inv i ≫ a) he)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.RefinementExt
