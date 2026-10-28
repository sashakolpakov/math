import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison

/-! # Cover Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinement

noncomputable section

/-! Actual refinement of an open cover preserves both edges of the
native injective Čech bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite Simplicial

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : TopCat.{u}} {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

def map (P : X.Presheaf AddCommGrpCat.{u}) :
    (cechComplexFunctor U).obj P ⟶ (cechComplexFunctor V).obj P :=
  GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r P

def intersectionHom (n : ℕ) (t : Fin (n + 1) → κ) :
    (∏ᶜ (V ∘ t)) ⟶ ∏ᶜ (U ∘ (r.f ∘ t)) :=
  ((FormalCoproduct.cechFunctor.map r).app (op ⦋n⦌)).φ t

theorem map_f_π (P : X.Presheaf AddCommGrpCat.{u}) (n : ℕ)
    (t : Fin (n + 1) → κ) :
    (CoverRefinement.map U V r P).f n ≫
      Pi.π (fun t : Fin (n + 1) → κ => P.obj (op (∏ᶜ (V ∘ t)))) t =
    Pi.π (fun s : Fin (n + 1) → ι => P.obj (op (∏ᶜ (U ∘ s)))) (r.f ∘ t) ≫
      P.map (intersectionHom U V r n t).op := by
  exact Pi.lift_comp_π _ t

theorem coordinates (P : X.Presheaf AddCommGrpCat.{u}) (n : ℕ)
    (x : ((cechComplexFunctor U).obj P).X n) (t : Fin (n + 1) → κ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains.cechCochainAddEquiv P V n ((CoverRefinement.map U V r P).f n x) t =
      P.map (intersectionHom U V r n t).op
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains.cechCochainAddEquiv P U n x (r.f ∘ t)) := by
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains.cechCochainAddEquiv_apply, AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains.cechCochainAddEquiv_apply]
  exact ConcreteCategory.congr_hom (map_f_π U V r P n t) x

theorem augmentation (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U ≫ (CoverRefinement.map U V r F.obj).f 0 =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F V := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains.cechCochainAddEquiv F.obj V 0).injective
  funext t
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains.cechCochainAddEquiv F.obj V 0
    ((CoverRefinement.map U V r F.obj).f 0 (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U x)) t = _
  rw [coordinates, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation_coordinate,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation_coordinate]
  change (F.obj.map _ ≫ F.obj.map _) _ = F.obj.map _ _
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans (congrArg F.obj.map (Subsingleton.elim _ _))) _

def bicomplexMap
    (K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveBicomplex.IntrinsicCech.cechBicomplex U K ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveBicomplex.IntrinsicCech.cechBicomplex V K where
  f q := CoverRefinement.map U V r (K.X q).obj
  comm' q q' _ :=
    (GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.naturality
      (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r (K.d q q').hom).symm

def totalMap (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).total (.up ℕ) ⟶
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex V F).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap U V r (injectiveResolution F).cocomplex) (.up ℕ)

theorem vertical (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge U F ≫ totalMap U V r F =
      CoverRefinement.map U V r F.obj ≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge V F := by
  apply HomologicalComplex.Hom.ext
  funext q
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge_f, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge_f]
  rw [Category.assoc, totalMap, HomologicalComplex₂.ιTotal_map]
  simp only [← Category.assoc]
  congr 1
  exact congrArg (fun a => a.f q)
    (GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.naturality
      (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r ((injectiveResolution F).ι.f 0).hom)

theorem horizontal (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge U F ≫ totalMap U V r F =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge V F := by
  apply HomologicalComplex.Hom.ext
  funext q
  rw [HomologicalComplex.comp_f, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge_f,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge_f, Category.assoc, totalMap, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc]
  exact congrArg
    (fun a => a ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex V F).ιTotal (.up ℕ) q 0 q rfl)
    (augmentation U V r ((injectiveResolution F).cocomplex.X q))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinement
