import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SourceNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.GlobalEdge

/-! # Frame Source Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameSourceNormalization

noncomputable section

/-! The native covering-frame comparison is normalized by the genuine
source-augmentation sections, for arbitrary intermediate complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u z
variable {C : Type u} [Category.{0} C] [HasBinaryProducts C]
  {ι : Type} [Finite ι] (F : ι → C) (R : Type u) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (hcover : ∀ V, CoveringObjectsSheafDetection.sieve F V ∈ J V)
  {Y : Sheaf J (ModuleCat.{u} R)} (I : InjectiveResolution Y)
  (K : CochainComplex (Sheaf J (ModuleCat.{u} R)) ℕ) (g : K ⟶ I.cocomplex)

local instance coproducts : HasCoproducts.{0} (ModuleCat.{max u z} R) :=
  fun T => (ModuleCat.hasColimitsOfSize.{max u z,u,0,0} R).has_colimits_of_shape (Discrete T)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.complex J R F
local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.augmentation J R F

omit [Finite ι] in
theorem total_natural : ResolutionHom.SourceNaturality.totalMap R P g ≫
    (FrameCech.ExtCoefficientEdge.totalIso.{u,0,z} F R J I.cocomplex).hom =
      (FrameCech.ExtCoefficientEdge.totalIso.{u,0,z} F R J K).hom ≫
        FrameCech.AugmentationNaturality.totalMap.{u,0,z} F R J K I.cocomplex g :=
  (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)).symm.trans
    ((congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ))
      (FrameCech.ExtBicomplex.naturality.{u,0,z} F R J K g)).trans
        (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)))

def edge := ResolutionHom.Total.edge R P ε K ≫
  (FrameCech.ExtCoefficientEdge.totalIso.{u,0,z} F R J K).hom

private theorem through_coordinates {A : Type*} [Category A]
    {U V V' W W' E : A} (a : U ⟶ V) (e : V ≅ V') (d : W ≅ W')
    (f : V ⟶ W) (g : V' ⟶ W') (c : W ⟶ E)
    (h : f ≫ d.hom = e.hom ≫ g) :
    (a ≫ e.hom) ≫ (g ≫ d.inv ≫ c) = a ≫ (f ≫ c) := by
  have hi := InverseCoordinateHomology.inverse e d f g h
  simp only [Category.assoc]
  rw [← Category.assoc g d.inv c, hi]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

abbrev source_homology (i : ℕ) := by
  let : QuasiIso ε := CoveringPresentationResolution.augmentation_quasiIso J R F hcover
  have hc := (HomologicalComplex.homologyMap_comp
    (ResolutionHom.SourceNaturality.totalMap R P g)
    (FrameCech.ExtCoefficientEdge.totalIso.{u,0,z} F R J I.cocomplex).hom i).symm.trans
    ((congrArg (fun a => HomologicalComplex.homologyMap a i) (total_natural F R J I K g)).trans
      (HomologicalComplex.homologyMap_comp
        (FrameCech.ExtCoefficientEdge.totalIso.{u,0,z} F R J K).hom
        (FrameCech.AugmentationNaturality.totalMap.{u,0,z} F R J K I.cocomplex g) i))
  have h := through_coordinates
    (HomologicalComplex.homologyMap (ResolutionHom.Total.edge R P ε K) i)
    (HomologicalComplex.homologyMapIso (FrameCech.ExtCoefficientEdge.totalIso.{u,0,z} F R J K) i)
    (HomologicalComplex.homologyMapIso (FrameCech.ExtCoefficientEdge.totalIso.{u,0,z} F R J I.cocomplex) i)
    (HomologicalComplex.homologyMap (ResolutionHom.SourceNaturality.totalMap R P g) i)
    (HomologicalComplex.homologyMap (FrameCech.AugmentationNaturality.totalMap.{u,0,z} F R J K I.cocomplex g) i)
    (ResolutionHom.Total.homologyIso R P ε I i).hom hc
  exact (congrArg (fun a => a ≫ FrameAugmentation.comparison.{u,0,z} F R J hcover I K g i)
    (HomologicalComplex.homologyMap_comp (ResolutionHom.Total.edge R P ε K)
      (FrameCech.ExtCoefficientEdge.totalIso.{u,0,z} F R J K).hom i)).trans
      (h.trans (SourceNormalization.source_edge R P ε I K g i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameSourceNormalization
