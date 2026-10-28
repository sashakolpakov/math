import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientCoordinates

/-! # Ambient Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal

noncomputable section

/-! The ambient-open coordinate isomorphism for whole coefficient
complexes, with its original naturality square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {X : TopCat.{u}} {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C)
  [∀ (n : ℕ) (z : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F]
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]

abbrev restriction : ((Opens X)ᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  (Functor.whiskeringLeft _ _ _).obj F.op

variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)

def bicomplexIso :
    AugmentedOrdered.CechFunctor.bicomplex U
      (((restriction F).mapHomologicalComplex (.up ℕ)).obj K) ≅
        RelativeCech.Total.source (F.obj (⊤_ C)) (F.obj ∘ U) K :=
  (NatIso.mapHomologicalComplex (AmbientCoordinates.functorIso F U) (.up ℕ)).app K

theorem bicomplexIso_hom_f (q n : ℕ) :
    ((bicomplexIso F U K).hom.f q).f n =
      (AmbientCoordinates.componentIso F U (K.X q) n).hom := rfl

variable [HasCoproducts.{0} D]

def totalIso :
    (AugmentedOrdered.CechFunctor.bicomplex U
      (((restriction F).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ) ≅
        (RelativeCech.Total.source (F.obj (⊤_ C)) (F.obj ∘ U) K).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso F U K) (.up ℕ)

theorem naturality {L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) :
    HomologicalComplex₂.total.map
      (((AugmentedOrdered.CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map
        (((restriction F).mapHomologicalComplex (.up ℕ)).map a)) (.up ℕ) ≫
          (totalIso F U L).hom =
    (totalIso F U K).hom ≫ RelativeCech.Total.sourceMap (F.obj (⊤_ C)) (F.obj ∘ U) a := by
  let T := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map
      ((NatIso.mapHomologicalComplex (AmbientCoordinates.functorIso F U)
        (.up ℕ)).hom.naturality a)).trans (T.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal
