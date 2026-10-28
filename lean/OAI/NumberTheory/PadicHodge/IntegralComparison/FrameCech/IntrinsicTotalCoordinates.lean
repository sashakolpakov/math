import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoefficientEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.CoefficientEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationEdge

/-! # Intrinsic Total Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.IntrinsicTotalCoordinates.Intrinsic

noncomputable section

/-! Native presheaf total coordinates for the balanced frame comparison.
The canonical coefficient lift retains its literal augmentation edge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {κ : Type v} (F : κ → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (K : CochainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ)
  {Y : Sheaf J (ModuleCat.{max u v} R)} (ι : (CochainComplex.single₀ _).obj Y ⟶ K)

private instance moduleCoproducts (S : Type*) [CommRing S] : HasCoproducts.{0} (ModuleCat.{z} S) :=
  fun T => (ModuleCat.hasColimitsOfSize.{z, _, 0, 0} S).has_colimits_of_shape (Discrete T)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve F
abbrev coefficients (S : Type u) [CommRing S] : ModuleCat.{u} S ⥤ ModuleCat.{max u v} S :=
  ModuleCat.uliftFunctor.{v, u} S

local instance smallLimits : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
local instance smallProducts : HasProducts.{v} (ModuleCat.{max u v} R) :=
  fun T => (smallLimits (R := R)).has_limits_of_shape (Discrete T)

def presheafComplex :=
  ((sheafToPresheaf J (ModuleCat.{max u v} R)).mapHomologicalComplex (.up ℕ)).obj K

def bicomplex := Presheaf.TotalCup.CechProduct.bicomplex.{max u v, v, v, u, max u v}
  N (presheafComplex.{u, v} R J K)

def totalIso : (ExtCoefficientEdge.bicomplex.{u, v, z} F R J K).total (.up ℕ) ≅
    ((coefficients.{max u v, z} R).mapHomologicalComplex (.up ℕ)).obj ((bicomplex.{u, v} F R J K).total (.up ℕ)) :=
  AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso (coefficients.{max u v, z} R) (bicomplex.{u, v} F R J K)

def rowMap : (NonemptyCechNerve.complexFunctor F).obj Y.obj ⟶ (bicomplex.{u, v} F R J K).X 0 :=
  (NonemptyCechNerve.complexFunctor F).map (ι.f 0).hom

omit [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))] in
theorem closed : rowMap.{u, v} F R J K ι ≫ (bicomplex.{u, v} F R J K).d 0 1 = 0 :=
  Presheaf.AugmentationEdge.closed.{max u v, v, v, u, max u v}
    N (presheafComplex.{u, v} R J K) Y.obj (ι.f 0).hom
    (congrArg (fun a : Y ⟶ K.X 1 => a.hom)
      (Augmented.ResolutionCycles.augmentation_condition K ι))

def edge : (NonemptyCechNerve.complexFunctor F).obj Y.obj ⟶
    (bicomplex.{u, v} F R J K).total (.up ℕ) :=
  BicomplexCoefficientEdge.edge (bicomplex.{u, v} F R J K)
  ((NonemptyCechNerve.complexFunctor F).obj Y.obj) (rowMap.{u, v} F R J K ι) (closed.{u, v} F R J K ι)

theorem edge_square : ExtCoefficientEdge.edge.{u, v, z} F R J K ι ≫
    (totalIso.{u, v, z} F R J K).hom =
      ((coefficients.{max u v, z} R).mapHomologicalComplex (.up ℕ)).map (edge.{u, v} F R J K ι) :=
  Additive.CoefficientEdge.comparison (coefficients.{max u v, z} R) (bicomplex.{u, v} F R J K)
    ((NonemptyCechNerve.complexFunctor F).obj Y.obj) (rowMap.{u, v} F R J K ι) (closed.{u, v} F R J K ι)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.IntrinsicTotalCoordinates.Intrinsic
