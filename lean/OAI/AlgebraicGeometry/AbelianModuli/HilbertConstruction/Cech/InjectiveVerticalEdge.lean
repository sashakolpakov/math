/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechInjectiveAugmentation.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveAugmentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.VerticalEdge

/-! # Injective Vertical Edge -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveVerticalEdge.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

theorem cechInjectiveResolutionAugmentation_comm
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p p' : ℕ)
    (_ : (ComplexShape.up ℕ).Rel p p') :
    (InjectiveAugmentation.IntrinsicCech.cechInjectiveResolutionAugmentation U F).f p ≫
        ((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).X 0).d p p' =
      ((cechComplexFunctor U).obj F.obj).d p p' ≫
        (InjectiveAugmentation.IntrinsicCech.cechInjectiveResolutionAugmentation U F).f p' := by
  exact HomologicalComplex.Hom.comm
    (InjectiveAugmentation.IntrinsicCech.cechInjectiveResolutionAugmentation U F) p p'

/-- The Cech complex of a sheaf maps into the total Cech complex of its chosen
injective resolution by the vertical edge. -/
noncomputable def cechInjectiveResolutionVerticalEdge
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (cechComplexFunctor U).obj F.obj ⟶
      (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).total (.up ℕ) :=
  TotalComplex.VerticalEdge.totalUpNatVerticalEdge (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F)
    ((cechComplexFunctor U).obj F.obj)
    (fun p ↦ (InjectiveAugmentation.IntrinsicCech.cechInjectiveResolutionAugmentation U F).f p)
    (cechInjectiveResolutionAugmentation_comm U F)
    (InjectiveAugmentation.IntrinsicCech.cechInjectiveResolutionAugmentation_f_comp_d U F)

@[simp]
theorem cechInjectiveResolutionVerticalEdge_f
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    (cechInjectiveResolutionVerticalEdge U F).f p =
      (InjectiveAugmentation.IntrinsicCech.cechInjectiveResolutionAugmentation U F).f p ≫
        (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).ιTotal
          (.up ℕ) 0 p p (zero_add p) := by
  apply TotalComplex.VerticalEdge.totalUpNatVerticalEdge_f

/-- The total-complex map induced by a cochain map between the chosen
injective resolutions. -/
noncomputable def cechInjectiveResolutionTotalMap
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (phi : (injectiveResolution F).cocomplex ⟶
      (injectiveResolution G).cocomplex) :
    (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).total (.up ℕ) ⟶
      (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U G).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplexMap U phi) (.up ℕ)

/-- The vertical Cech edge commutes with a morphism between chosen injective
resolutions that lifts a morphism of sheaves. -/
theorem cechInjectiveResolutionVerticalEdge_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)
    (phi : InjectiveResolution.Hom
      (injectiveResolution F)
      (injectiveResolution G) f) :
    cechInjectiveResolutionVerticalEdge U F ≫
        cechInjectiveResolutionTotalMap U phi.hom =
      (cechComplexFunctor U).map f.hom ≫
        cechInjectiveResolutionVerticalEdge U G := by
  apply HomologicalComplex.Hom.ext
  funext p
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    cechInjectiveResolutionVerticalEdge_f,
    cechInjectiveResolutionVerticalEdge_f]
  rw [Category.assoc, cechInjectiveResolutionTotalMap,
    HomologicalComplex₂.ιTotal_map]
  simp only [← Category.assoc]
  congr 1
  change
    (((cechComplexFunctor U).map
          ((injectiveResolution F).ι.f 0).hom) ≫
        (cechComplexFunctor U).map (phi.hom.f 0).hom).f p =
      (((cechComplexFunctor U).map f.hom ≫
          (cechComplexFunctor U).map
            ((injectiveResolution G).ι.f 0).hom).f p)
  let a := ((injectiveResolution F).ι.f 0).hom
  let b := (phi.hom.f 0).hom
  let c := f.hom
  let d := ((injectiveResolution G).ι.f 0).hom
  have hphi : a ≫ b = c ≫ d :=
    congrArg (fun g ↦ g.hom) phi.ι_f_zero_comp_hom_f_zero
  have hmap :
      (cechComplexFunctor U).map a ≫ (cechComplexFunctor U).map b =
        (cechComplexFunctor U).map c ≫ (cechComplexFunctor U).map d :=
    ((cechComplexFunctor U).map_comp a b).symm.trans
      ((congrArg (cechComplexFunctor U).map hphi).trans
        ((cechComplexFunctor U).map_comp c d))
  exact congrArg (fun g ↦ g.f p) hmap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveVerticalEdge.IntrinsicCech
