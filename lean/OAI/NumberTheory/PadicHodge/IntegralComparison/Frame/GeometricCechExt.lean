import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainMixedNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.GeometricCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.CosimplicialRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Geometric Cech Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.GeometricCechExt

noncomputable section

/-! Native tuple pullback under a genuine geometric frame map computes
the exact-functor and source maps on original Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v z

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  (T : C ⥤ D) {ι κ : Type v} (F : ι → C) (G : κ → D) (ρ : ι → κ)
  (α : ∀ i, T.obj (F i) ⟶ G (ρ i))
  (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [T.IsContinuous J K] [T.IsCocontinuous J K]
  [∀ (M : Cᵒᵖ ⥤ ModuleCat.{max u v} R), T.op.HasPointwiseRightKanExtension M]
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  [HasExt.{max u v z} (Sheaf K (ModuleCat.{max u v} R))]
  (H : Sheaf K (ModuleCat.{max u v} R))

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafRestriction.restriction R T J K

local instance restriction_linear : (S).Linear R where
  map_smul := by intros; rfl

local instance restriction_leftAdjoint : (S).IsLeftAdjoint :=
  (T.sheafAdjunctionCocontinuous (ModuleCat.{max u v} R) J K).isLeftAdjoint

local instance restriction_finiteLimits : PreservesFiniteLimits S := by
  change PreservesFiniteLimits (T.sheafPushforwardContinuous (ModuleCat.{max u v} R) J K)
  infer_instance

local instance restriction_finiteColimits : PreservesFiniteColimits S := by infer_instance

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

def coefficient (n : ℕ) (t : Fin (n + 1) → ι) :=
  H.obj.map (TupleRefinement.map T F G ρ α n t).op

omit [∀ (M : Cᵒᵖ ⥤ ModuleCat.{max u v} R), T.op.HasPointwiseRightKanExtension M]
  [HasExt.{max u v z} (Sheaf K (ModuleCat.{max u v} R))] in
theorem coefficient_naturality (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → ι) :
    coefficient T F G ρ α R K H b (t ∘ θ) ≫
      (T.op ⋙ H.obj).map (Presentation.ResolutionFaceMaps.productMap F θ t).op =
        H.obj.map (Presentation.ResolutionFaceMaps.productMap G θ (ρ ∘ t)).op ≫
          coefficient T F G ρ α R K H a t :=
  (H.obj.map_comp (TupleRefinement.map T F G ρ α b (t ∘ θ)).op
    (T.map (Presentation.ResolutionFaceMaps.productMap F θ t)).op).symm.trans
      ((congrArg (fun z => H.obj.map z.op) (TupleRefinement.naturality T F G ρ α a b θ t)).trans
        (H.obj.map_comp (Presentation.ResolutionFaceMaps.productMap G θ (ρ ∘ t)).op
          (TupleRefinement.map T F G ρ α a t).op))

def cochainMap : FrameCech.Differential.complex G R H.obj ⟶
    FrameCech.Differential.complex F R ((S).obj H).obj :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).map
    (CosimplicialRefinement.map G F ρ H.obj (T.op ⋙ H.obj)
      (coefficient T F G ρ α R K H) (coefficient_naturality T F G ρ α R K H))

omit [T.IsCocontinuous J K] [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  [∀ (M : Cᵒᵖ ⥤ ModuleCat.{max u v} R), T.op.HasPointwiseRightKanExtension M]
  [HasExt.{max u v z} (Sheaf K (ModuleCat.{max u v} R))] in
theorem cochainMap_coordinate (n : ℕ) (t : Fin (n + 1) → ι) :
    (cochainMap T F G ρ α R J K H).f n ≫
      FrameCech.Differential.coordinate F R ((S).obj H).obj n t =
        FrameCech.Differential.coordinate G R H.obj n (ρ ∘ t) ≫
          H.obj.map (TupleRefinement.map T F G ρ α n t).op := Pi.lift_comp_π _ t

def liftedMap : FrameCech.Ext.Comparison.liftedComplex.{u, v, z} G R K H ⟶
    FrameCech.Ext.Comparison.liftedComplex.{u, v, z} F R J ((S).obj H) :=
  ((ModuleCat.uliftFunctor.{z, max u v} R).mapHomologicalComplex (.up ℕ)).map
    (cochainMap T F G ρ α R J K H)

def resolutionMap := Acyclic.ChainFunctorNaturality.map S R H
  (CoveringPresentationResolution.complex K R G) (CoveringPresentationResolution.complex J R F)
    (Presentation.GeometricRefinement.map T F G ρ α R J K)

theorem coordinate (n : ℕ) (t : Fin (n + 1) → ι)
    (f : (CoveringPresentationResolution.complex K R G).X n ⟶ H) :
    FrameCech.Differential.coordinate F R ((S).obj H).obj n t
      (((FrameCech.Ext.Comparison.comparison F R J ((S).obj H)).hom.f n
        ((resolutionMap T F G ρ α R J K H).f n (Abelian.Ext.mk₀ f))).down) =
      FrameCech.Differential.coordinate F R ((S).obj H).obj n t
        (((liftedMap T F G ρ α R J K H).f n
          ((FrameCech.Ext.Comparison.comparison G R K H).hom.f n (Abelian.Ext.mk₀ f))).down) := by
  have hm := Acyclic.ChainFunctorCoordinates.map_mk S R H
    (CoveringPresentationResolution.complex K R G) (CoveringPresentationResolution.complex J R F)
    (Presentation.GeometricRefinement.map T F G ρ α R J K) n f
  have hl := (congrArg (fun x => FrameCech.Differential.coordinate F R ((S).obj H).obj n t
    (((FrameCech.Ext.Comparison.comparison F R J ((S).obj H)).hom.f n x).down)) hm).trans
      ((FrameCech.ExtCoordinates.coordinate_mk F R J ((S).obj H) n t
        ((Presentation.GeometricRefinement.map T F G ρ α R J K).f n ≫ (S).map f)).trans
          (Presentation.GeometricCoordinates.sheaf T F G ρ α n t R J K H f))
  have hr := (congrArg (fun a => a
    (((FrameCech.Ext.Comparison.comparison G R K H).hom.f n (Abelian.Ext.mk₀ f)).down))
      (cochainMap_coordinate T F G ρ α R J K H n t)).trans
        (congrArg (H.obj.map (TupleRefinement.map T F G ρ α n t).op)
          (FrameCech.ExtCoordinates.coordinate_mk G R K H n (ρ ∘ t) f))
  exact hl.trans hr.symm

theorem complexes : resolutionMap T F G ρ α R J K H ≫
    (FrameCech.Ext.Comparison.comparison F R J ((S).obj H)).hom =
      (FrameCech.Ext.Comparison.comparison G R K H).hom ≫ liftedMap T F G ρ α R J K H := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Abelian.Ext.{max u v z} ((CoveringPresentationResolution.complex K R G).X n) H 0 at x
  obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
  apply ULift.ext
  apply Module.ProductScalarKernel.element_ext
    (fun t => ((S).obj H).obj.obj (op (Presentation.TupleProducts.family F n t)))
  intro t
  exact coordinate T F G ρ α R J K H n t f

variable [QuasiIso (CoveringPresentationResolution.augmentation J R F)]
  [QuasiIso (CoveringPresentationResolution.augmentation K R G)]

omit [HasBinaryProducts C] [HasBinaryProducts D] in
theorem resolution_homology
  (sourceAcyclicity : ∀ a q, Subsingleton (Abelian.Ext.{max u v z}
    ((CoveringPresentationResolution.complex J R F).X a) ((S).obj H) (q + 1)))
  (targetAcyclicity : ∀ a q, Subsingleton (Abelian.Ext.{max u v z}
    ((CoveringPresentationResolution.complex K R G).X a) H (q + 1)))
    (i : ℕ) : HomologicalComplex.homologyMap
    (resolutionMap.{u, v, z} T F G ρ α R J K H) i ≫
      (Acyclic.ChainCohomology.homologyIso.{max (u + 1) (v + 1), max u v, max u v z, max u v}
        (Z := (constantSheaf J (ModuleCat.{max u v} R)).obj (ModuleCat.of R R)) R ((S).obj H) (CoveringPresentationResolution.complex J R F)
        (CoveringPresentationResolution.augmentation J R F) (fun a q => sourceAcyclicity a q) i).hom =
    (Acyclic.ChainCohomology.homologyIso.{max (u + 1) (v + 1), max u v, max u v z, max u v}
      (Z := (constantSheaf K (ModuleCat.{max u v} R)).obj (ModuleCat.of R R)) R H (CoveringPresentationResolution.complex K R G)
      (CoveringPresentationResolution.augmentation K R G) (fun a q => targetAcyclicity a q) i).hom ≫
        IntegralComparison.Ext.SourceExactFunctorModule.component.{max (u + 1) (v + 1), max u v, max (u + 1) (v + 1), max u v, max u v z, max u v} S R H i
          (op ((constantSheaf K (ModuleCat.{max u v} R)).obj (ModuleCat.of R R))) ≫
          (IntegralComparison.Ext.ContravariantModuleFunctor.functor.{max (u + 1) (v + 1), max u v, max u v z, max u v} R ((S).obj H) i).map
            (Cech.PresentationSheafRestriction.constantIso R T J K).inv.op :=
  Acyclic.ChainMixedNaturality.homology.{max (u + 1) (v + 1), max u v, max (u + 1) (v + 1), max u v, max u v z, max u v}
    (Z := (constantSheaf K (ModuleCat.{max u v} R)).obj (ModuleCat.of R R))
    (W := (constantSheaf J (ModuleCat.{max u v} R)).obj (ModuleCat.of R R)) S R H
    (CoveringPresentationResolution.complex K R G) (CoveringPresentationResolution.complex J R F)
    (Presentation.GeometricRefinement.map T F G ρ α R J K)
    (CoveringPresentationResolution.augmentation K R G) (CoveringPresentationResolution.augmentation J R F)
    (Cech.PresentationSheafRestriction.constantIso R T J K).inv
    (Presentation.GeometricRefinement.augmentation_zero T F G ρ α R J K) targetAcyclicity sourceAcyclicity i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.GeometricCechExt
