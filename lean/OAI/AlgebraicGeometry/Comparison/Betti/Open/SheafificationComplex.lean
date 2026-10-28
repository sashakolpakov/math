import OAI.AlgebraicGeometry.Comparison.Betti.Open.Image
import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness

/-! # Sheafification Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.SheafificationComplex

noncomputable section

/-! Normalize sheafification and restriction on integer complexes via their actual adjunctions. -/

open _root_.CategoryTheory _root_.TopologicalSpace

def topologicalSheafificationAdjunctionInt (M : TopCat.{0}) :
    (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⊣
      (sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  Complex.Adjunction.onComplexes
    (sheafificationAdjunction (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)) (ComplexShape.up ℤ)

variable {M N : TopCat.{0}} (f : M ⟶ N) (hf : Topology.IsOpenEmbedding f)

def openPresheafAdjunctionInt :
    (Image.openPresheafRestriction f hf).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (Image.openPresheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Complex.Adjunction.onComplexes (Image.openPresheafAdjunction f hf) (ComplexShape.up ℤ)

def openRestrictionAdjunctionInt :
    (Image.openRestriction f hf).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Complex.Adjunction.onComplexes (Image.openRestrictionAdjunction f hf) (ComplexShape.up ℤ)

def sheafificationOpenRestrictionComplexIso :
    (presheafToSheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ (Image.openRestriction f hf).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (Image.openPresheafRestriction f hf).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  ((topologicalSheafificationAdjunctionInt N).comp (openRestrictionAdjunctionInt f hf)).leftAdjointUniq
    ((openPresheafAdjunctionInt f hf).comp (topologicalSheafificationAdjunctionInt M))

variable {P : CochainComplex (N.Presheaf (ModuleCat.{0} ℂ)) ℤ}
  {Q : CochainComplex (M.Presheaf (ModuleCat.{0} ℂ)) ℤ}
  (p : P ⟶ ((Image.openPresheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)

def sheafifiedOpenDirectMapInt :
    ((presheafToSheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶
    ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q) :=
  ((topologicalSheafificationAdjunctionInt N).homEquiv _ _).symm
    (p ≫ ((Image.openPresheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((topologicalSheafificationAdjunctionInt M).unit.app Q))

def sheafifiedOpenPullbackInt :
    ((Image.openRestriction f hf).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((presheafToSheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ⟶
    ((presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Q :=
  ((openRestrictionAdjunctionInt f hf).homEquiv _ _).symm (sheafifiedOpenDirectMapInt f p)

theorem sheafifiedOpenPullbackInt_normalization :
    sheafifiedOpenPullbackInt f hf p =
      (sheafificationOpenRestrictionComplexIso f hf).hom.app P ≫
        ((presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (((openPresheafAdjunctionInt f hf).homEquiv P Q).symm p) := by
  let a := topologicalSheafificationAdjunctionInt N
  let b := openRestrictionAdjunctionInt f hf
  let c := openPresheafAdjunctionInt f hf
  let d := topologicalSheafificationAdjunctionInt M
  let LN := (presheafToSheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let LM := (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let Dp := (Image.openPresheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℤ)
  let Ds := (TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℤ)
  let r := (c.homEquiv P Q).symm p
  have hp : c.homEquiv P Q r = p := (c.homEquiv P Q).apply_symm_apply p
  have h₁ : b.homEquiv (LN.obj P) (LM.obj Q) (sheafifiedOpenPullbackInt f hf p) =
      sheafifiedOpenDirectMapInt f p := (b.homEquiv _ _).apply_symm_apply _
  have h₂ : a.homEquiv P (Ds.obj (LM.obj Q)) (sheafifiedOpenDirectMapInt f p) = p ≫ Dp.map (d.unit.app Q) :=
    (a.homEquiv _ _).apply_symm_apply _
  have hl : (a.comp b).homEquiv P (LM.obj Q) (sheafifiedOpenPullbackInt f hf p) =
      p ≫ Dp.map (d.unit.app Q) :=
    (congrArg (a.homEquiv P (Ds.obj (LM.obj Q))) h₁).trans h₂
  have hr := AdjunctionComplexUniqueness.comp_homEquiv_map_comp c d r (𝟙 (LM.obj Q))
  erw [Category.comp_id, hp, d.homEquiv_id] at hr
  have he := AdjunctionComplexUniqueness.leftAdjointUniq_homEquiv (a.comp b) (c.comp d) (LM.map r)
  apply ((a.comp b).homEquiv P (LM.obj Q)).injective
  exact hl.trans (he.trans hr).symm

theorem sheafifiedOpenPullbackInt_isIso
    [IsIso (((openPresheafAdjunctionInt f hf).homEquiv P Q).symm p)] :
    IsIso (sheafifiedOpenPullbackInt f hf p) := by
  rw [sheafifiedOpenPullbackInt_normalization]
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.SheafificationComplex
