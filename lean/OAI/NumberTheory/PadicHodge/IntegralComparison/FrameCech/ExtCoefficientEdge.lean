import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtBicomplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.CoefficientEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexCoefficientEdge

/-! # Ext Coefficient Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoefficientEdge

noncomputable section

/-! The original mixed-resolution coefficient augmentation is literally
the native frame Čech augmentation after the established section coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {κ : Type v} (F : κ → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (K : CochainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ)
  {Y : Sheaf J (ModuleCat.{max u v} R)} (ι : (CochainComplex.single₀ _).obj Y ⟶ K)

universe w w'
local instance moduleCoproducts (R' : Type w) [Ring R'] :
    HasCoproducts.{0} (ModuleCat.{w'} R') :=
  fun I => (ModuleCat.hasColimitsOfSize.{w', w, 0, 0} R').has_colimits_of_shape (Discrete I)

def bicomplex : HomologicalComplex₂ (ModuleCat.{max u v z} R) (.up ℕ) (.up ℕ) :=
  ((ExtBicomplex.liftedFunctor.{u, v, z} F R J).mapHomologicalComplex (.up ℕ)).obj K

def rowMap : Ext.Comparison.liftedComplex.{u, v, z} F R J Y ⟶
    (bicomplex.{u, v, z} F R J K).X 0 :=
  (ExtBicomplex.liftedFunctor.{u, v, z} F R J).map (ι.f 0)

theorem closed : rowMap.{u, v, z} F R J K ι ≫ (bicomplex.{u, v, z} F R J K).d 0 1 = 0 :=
  ((ExtBicomplex.liftedFunctor.{u, v, z} F R J).map_comp _ _).symm.trans
    ((congrArg (ExtBicomplex.liftedFunctor.{u, v, z} F R J).map
      (Augmented.ResolutionCycles.augmentation_condition K ι)).trans
        ((ExtBicomplex.liftedFunctor.{u, v, z} F R J).map_zero _ _))

def edge : Ext.Comparison.liftedComplex.{u, v, z} F R J Y ⟶
    (bicomplex.{u, v, z} F R J K).total (.up ℕ) :=
  BicomplexCoefficientEdge.edge _ _ (rowMap.{u, v, z} F R J K ι) (closed.{u, v, z} F R J K ι)

def totalIso :
    ResolutionHom.Total.total R (CoveringPresentationResolution.complex J R F) K ≅
      (bicomplex.{u, v, z} F R J K).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (ExtBicomplex.bicomplexIso.{u, v, z} F R J K) (.up ℕ)

theorem square :
    ResolutionHom.CoefficientEdge.edge R (CoveringPresentationResolution.complex J R F) K ι ≫
      (totalIso.{u, v, z} F R J K).hom =
        (Ext.Comparison.comparison.{u, v, z} F R J Y).hom ≫ edge.{u, v, z} F R J K ι :=
  BicomplexCoefficientEdge.naturality _ _
    (ResolutionHom.CoefficientEdge.rowMap R (CoveringPresentationResolution.complex J R F) K ι)
    (ResolutionHom.CoefficientEdge.closed R (CoveringPresentationResolution.complex J R F) K ι)
    _ (rowMap.{u, v, z} F R J K ι) (closed.{u, v, z} F R J K ι)
    (ExtBicomplex.bicomplexIso.{u, v, z} F R J K).hom
    (Ext.Comparison.comparison.{u, v, z} F R J Y).hom
    (CoefficientNaturality.complexes.{u, v, z} F R J (ι.f 0))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoefficientEdge
