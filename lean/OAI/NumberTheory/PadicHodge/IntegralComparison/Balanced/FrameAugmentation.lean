import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameCechCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.AugmentationNaturality

/-! # Frame Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameAugmentation

noncomputable section

/-! The balanced original Ext comparison is normalized by the literal
coefficient augmentation into any augmented frame sheaf complex equipped
with a map to an injective resolution. -/

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

theorem coefficient_edge (i : ℕ) :
    HomologicalComplex.homologyMap
        (FrameCech.ExtCoefficientEdge.edge.{u, v, z} F R J I.cocomplex I.ι) i ≫
      (FrameCechCohomology.totalHomologyIso.{u, v, z} F R J hcover I i).hom =
        (FrameCechCohomology.homologyIso.{u, v, z} F R J hcover I hP i).hom := by
  let P := CoveringPresentationResolution.complex J R F
  let e := CoveringPresentationResolution.augmentation J R F
  let : QuasiIso e := CoveringPresentationResolution.augmentation_quasiIso J R F hcover
  have H := InverseCoordinateHomology.homology
    (FrameCech.Ext.Comparison.comparison.{u, v, z} F R J Y)
    (FrameCech.ExtCoefficientEdge.totalIso.{u, v, z} F R J I.cocomplex)
    (ResolutionHom.CoefficientEdge.edge R P I.cocomplex I.ι)
    (FrameCech.ExtCoefficientEdge.edge.{u, v, z} F R J I.cocomplex I.ι)
    (FrameCech.ExtCoefficientEdge.square.{u, v, z} F R J I.cocomplex I.ι) i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ (ResolutionHom.Total.homologyIso R P e I i).hom) H).trans
      (Category.assoc _ _ _))

def comparison (i : ℕ) :
    ((FrameCech.ExtCoefficientEdge.bicomplex.{u, v, z} F R J K).total (.up ℕ)).homology i ⟶
      ModuleCat.of R (Abelian.Ext.{max u v z}
        ((constantSheaf J (ModuleCat R)).obj (ModuleCat.of R R)) Y i) :=
  HomologicalComplex.homologyMap
    (FrameCech.AugmentationNaturality.totalMap.{u, v, z} F R J K I.cocomplex g) i ≫
      (FrameCechCohomology.totalHomologyIso.{u, v, z} F R J hcover I i).hom

include h in
theorem augmentation_homology (i : ℕ) :
    HomologicalComplex.homologyMap (FrameCech.ExtCoefficientEdge.edge.{u, v, z} F R J K a) i ≫
      comparison.{u, v, z} F R J hcover I K g i =
        (FrameCechCohomology.homologyIso.{u, v, z} F R J hcover I hP i).hom := by
  have H := (HomologicalComplex.homologyMap_comp
    (FrameCech.ExtCoefficientEdge.edge.{u, v, z} F R J K a)
    (FrameCech.AugmentationNaturality.totalMap.{u, v, z} F R J K I.cocomplex g) i).symm.trans
      (congrArg (fun b => HomologicalComplex.homologyMap b i)
        (FrameCech.AugmentationNaturality.square.{u, v, z} F R J K I.cocomplex a I.ι g h))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫
      (FrameCechCohomology.totalHomologyIso.{u, v, z} F R J hcover I i).hom) H).trans
        (coefficient_edge.{u, v, z} F R J hcover I hP i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameAugmentation
