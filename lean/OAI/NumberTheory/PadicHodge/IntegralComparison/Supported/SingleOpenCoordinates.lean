import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.MappedSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.FunctorCoordinates

/-! # Single Open Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleOpenCoordinates

noncomputable section

/-! The original single-sheaf coordinates commute with genuine open
restriction, equality of open diagrams, and principal reindexing. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_left {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (a : B ⟶ D) (b : A ⟶ D) (h : e.hom ≫ a = b) :
    e.inv ≫ b = a := by rw [← h, Iso.inv_hom_id_assoc]

variable {Y : Scheme.{0}} {C : Type} [Preorder C] [HasFiniteProducts C]
  {ι : Type} [LinearOrder ι] (W : ι → C) (F : C ⥤ Y.Opens)
  (N : Y.Modules) (c m : ℕ)

abbrev sections : Y.Opensᵒᵖ ⥤ AddCommGrpCat :=
  ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N).obj

abbrev originalSingle : CochainComplex (Y.Opensᵒᵖ ⥤ AddCommGrpCat) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
    ((single _ (.up ℕ) c).obj (AffinePrincipal.Injective.Comparison.sheaf N))

abbrev coordinates := IntegralComparison.Functor.SingleTotal.homologyIso
  (AffinePrincipal.Injective.Comparison.coefficients F ⋙ AugmentedOrdered.CechFunctor.functor W)
  (AffinePrincipal.Injective.Comparison.sheaf N) c m

theorem source_coordinates :
    (SingleCoefficientCoordinates.sourceIso W F N c (m+c)).hom ≫
      (coordinates W F N c m).hom =
    (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W)
      (F.op ⋙ sections N) c m).hom :=
  inverse_left (SingleCoefficientCoordinates.sourceIso W F N c (m+c)).symm _ _
    (IntegralComparison.Functor.MappedSingleCoordinates.comparison
      (AffinePrincipal.Injective.Comparison.coefficients F)
      (AugmentedOrdered.CechFunctor.functor W)
      (AffinePrincipal.Injective.Comparison.sheaf N) c m)

theorem restriction (G : C ⥤ Y.Opens) (α : G ⟶ F) :
    homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c) (m+c) ≫
      (coordinates W G N c m).hom =
    (coordinates W F N c m).hom ≫
      homologyMap (AugmentedOrdered.CechFunctor.complexMap W
        (Functor.whiskerRight (NatTrans.op α) (sections N))) m :=
  IntegralComparison.Functor.SingleMapCoordinates.naturality
    (AffinePrincipal.Injective.Comparison.coefficients F ⋙ AugmentedOrdered.CechFunctor.functor W)
    (AffinePrincipal.Injective.Comparison.coefficients G ⋙ AugmentedOrdered.CechFunctor.functor W)
    (Functor.whiskerRight (AffinePrincipal.InjectiveRestriction.coefficientsMap F G α)
      (AugmentedOrdered.CechFunctor.functor W))
    (AffinePrincipal.Injective.Comparison.sheaf N) c m

theorem congruence {G : C ⥤ Y.Opens} (e : F = G) :
    homologyMap (Principal.PresheafFunctorCongruence.sourceIso F e W
      (originalSingle N c)).hom (m+c) ≫
      (coordinates W G N c m).hom =
    (coordinates W F N c m).hom ≫
      homologyMap (AugmentedOrdered.CechFunctor.complexMap W
        (Open.FunctorCoordinates.presheafIso F e (sections N)).hom) m := by
  subst G
  simp only [Principal.PresheafFunctorCongruence.sourceIso,
    Open.FunctorCoordinates.presheafIso, eqToIso_refl, Iso.refl_hom,
    homologyMap_id, Category.id_comp]
  change _ = _ ≫ homologyMap ((AugmentedOrdered.CechFunctor.functor W).map (𝟙 _)) m
  rw [CategoryTheory.Functor.map_id, homologyMap_id, Category.comp_id]

variable {D : Type} [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r] (G : D ⥤ Y.Opens)

abbrev nativeComplex := ((AffinePrincipal.Injective.Comparison.coefficients G).mapHomologicalComplex
  (.up ℕ)).obj ((single _ (.up ℕ) c).obj (AffinePrincipal.Injective.Comparison.sheaf N))

theorem reindex_row :
    ((AugmentedOrdered.CechReindexTotal.bicomplexIso r W (nativeComplex N c G)).hom).f c ≫
      (IntegralComparison.Functor.SingleTotal.rowIso
        (AffinePrincipal.Injective.Comparison.coefficients G ⋙
          AugmentedOrdered.CechFunctor.functor (r.obj ∘ W))
        (AffinePrincipal.Injective.Comparison.sheaf N) c).hom =
    (IntegralComparison.Functor.SingleTotal.rowIso
      (AffinePrincipal.Injective.Comparison.coefficients (r ⋙ G) ⋙ AugmentedOrdered.CechFunctor.functor W)
      (AffinePrincipal.Injective.Comparison.sheaf N) c).hom ≫
      (AugmentedOrdered.CechReindex.iso r W (G.op ⋙ sections N)).hom := by
  exact (AugmentedOrdered.CechReindex.naturality r W _
    ((AffinePrincipal.Injective.Comparison.coefficients G).map
      (singleObjXSelf (.up ℕ) c (AffinePrincipal.Injective.Comparison.sheaf N)).hom)).symm

theorem reindex :
    homologyMap (AugmentedOrdered.CechReindexTotal.totalIso r W (nativeComplex N c G)).hom (m+c) ≫
      (coordinates (r.obj ∘ W) G N c m).hom =
    (coordinates W (r ⋙ G) N c m).hom ≫
      homologyMap (AugmentedOrdered.CechReindex.iso r W (G.op ⋙ sections N)).hom m :=
  IntegralComparison.Functor.SingleMapCoordinates.comparison
    (AffinePrincipal.Injective.Comparison.coefficients (r ⋙ G) ⋙ AugmentedOrdered.CechFunctor.functor W)
    (AffinePrincipal.Injective.Comparison.coefficients G ⋙ AugmentedOrdered.CechFunctor.functor (r.obj ∘ W))
    (AffinePrincipal.Injective.Comparison.sheaf N) (AffinePrincipal.Injective.Comparison.sheaf N) c
    (AugmentedOrdered.CechReindexTotal.bicomplexIso r W (nativeComplex N c G)).hom
    (AugmentedOrdered.CechReindex.iso r W (G.op ⋙ sections N)).hom (reindex_row W N c r G) m

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleOpenCoordinates
