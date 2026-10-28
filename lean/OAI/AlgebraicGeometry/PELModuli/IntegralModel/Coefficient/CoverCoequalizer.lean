import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericFamilyCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceMorphismSpecialization

/-! # Cover Coequalizer -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CoverCoequalizer

noncomputable section

section

/-! The actual generic cover/base equation extends to one coefficient
enlargement, with the original arithmetic schemes kept as fixed sources. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Coefficients

theorem coefficient_cover_commutes_after_enlargement
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (X W : Over (Spec (.of R)))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom)
    {Y : Over (Spec (.of K))} (M : Models.Coefficients.CoefficientModel R K Y)
    (a : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj W ⟶ Y)
    (v : W ⟶ X) (hv : q ≫ a = (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map v)
    (a₀ : M.model ⟶ (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj X)
    (q₀ : (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj W ⟶ M.model)
    (ha : M.specialization ≫ a₀.left = a.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX).specialization)
    (hq : (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients W hW).specialization ≫ q₀.left = q.left ≫ M.specialization) :
    ∃ (t : Finset K) (hst : M.coefficients ⊆ t),
      (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W).inv ≫
          (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).map (q₀ ≫ a₀) ≫
          (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst X).hom =
        (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)).map v := by
  let s := M.coefficients
  let G := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let P := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)
  let MW := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K s W hW
  let MX := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K s X hX
  have hv' : q.left ≫ a.left = (G.map v).left := congrArg Over.Hom.left hv
  have heq : MW.specialization ≫ (q₀ ≫ a₀).left = MW.specialization ≫ (P.map v).left := by
    change MW.specialization ≫ (q₀.left ≫ a₀.left) = _
    calc
      _ = (q.left ≫ M.specialization) ≫ a₀.left :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ a₀.left) hq)
      _ = (q.left ≫ a.left) ≫ MX.specialization :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun k => q.left ≫ k) ha).trans (Category.assoc _ _ _).symm)
      _ = (G.map v).left ≫ MX.specialization := congrArg (fun k => k ≫ MX.specialization) hv'
      _ = _ := (Fixed.SourceMorphismSpecialization.Coefficients.fixedSourceModel_specialization_map s W X hW hX v).symm
  obtain ⟨t, hst, ht⟩ := Morphisms.Coefficients.equation_between_models_descends (s := M.coefficients) (X := G.obj W) MW.model MX.model
    MW.finitePresentation MX.finitePresentation MW.specialization MW.cartesian (q₀ ≫ a₀) (P.map v) heq
  have ht' := FiniteEquations.Coefficients.baseChange_map_eq_of_fst_eq hst MW.model MX.model (q₀ ≫ a₀) (P.map v) ht
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
    (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t) (Fixed.CoefficientModels.Coefficients.coefficient_parameterBaseMap R K hst)
  have hn : F.map (P.map v) ≫ (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst X).hom =
      (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W).hom ≫ (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)).map v :=
    e.hom.naturality v
  refine ⟨t, hst, ?_⟩
  change _ ≫ F.map (q₀ ≫ a₀) ≫ _ = _
  rw [ht', hn, Iso.inv_hom_id_assoc]

end Coefficients

end

/-! An actual generic coequalizer equation for a fixed arithmetic relation
extends over a finite coefficient enlargement. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Coefficients

theorem coefficient_cover_coequalizes_after_enlargement
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (Z W : Over (Spec (.of R)))
    (hZ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Z.hom) (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom)
    {Y : Over (Spec (.of K))} (M : Models.Coefficients.CoefficientModel R K Y)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj W ⟶ Y)
    (v w : Z ⟶ W)
    (hv : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map v ≫ q =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map w ≫ q)
    (q₀ : (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj W ⟶ M.model)
    (hq : (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients W hW).specialization ≫ q₀.left =
      q.left ≫ M.specialization) :
    ∃ (t : Finset K) (hst : M.coefficients ⊆ t),
      let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
      let P := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)
      let q₁ := (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W).inv ≫ F.map q₀
      P.map v ≫ q₁ = P.map w ≫ q₁ := by
  let s := M.coefficients
  let G := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let P := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)
  let MZ := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K s Z hZ
  let MW := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K s W hW
  have htrans (r : Z ⟶ W) :
      MZ.specialization ≫ (P.map r ≫ q₀).left =
        (G.map r ≫ q).left ≫ M.specialization := by
    change MZ.specialization ≫ ((P.map r).left ≫ q₀.left) =
      ((G.map r).left ≫ q.left) ≫ M.specialization
    calc
      _ = ((G.map r).left ≫ MW.specialization) ≫ q₀.left :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ q₀.left)
            (Fixed.SourceMorphismSpecialization.Coefficients.fixedSourceModel_specialization_map s Z W hZ hW r))
      _ = _ := (Category.assoc _ _ _).trans
        ((congrArg (fun k => (G.map r).left ≫ k) hq).trans (Category.assoc _ _ _).symm)
  have heq : MZ.specialization ≫ (P.map v ≫ q₀).left =
      MZ.specialization ≫ (P.map w ≫ q₀).left :=
    (htrans v).trans ((congrArg (fun k => k.left ≫ M.specialization) hv).trans (htrans w).symm)
  obtain ⟨t, hst, ht⟩ := Morphisms.Coefficients.equation_between_models_descends
    (s := M.coefficients) (X := G.obj Z) MZ.model M.model
    MZ.finitePresentation M.finitePresentation MZ.specialization MZ.cartesian
    (P.map v ≫ q₀) (P.map w ≫ q₀) heq
  have ht' := FiniteEquations.Coefficients.baseChange_map_eq_of_fst_eq hst MZ.model M.model
    (P.map v ≫ q₀) (P.map w ≫ q₀) ht
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let P' := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst) (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)
    (Fixed.CoefficientModels.Coefficients.coefficient_parameterBaseMap R K hst)
  have hn (r : Z ⟶ W) :
      P'.map r ≫ (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W).inv =
        (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst Z).inv ≫ F.map (P.map r) :=
    e.inv.naturality r
  refine ⟨t, hst, ?_⟩
  change P'.map v ≫ ((Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W).inv ≫ F.map q₀) =
    P'.map w ≫ ((Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W).inv ≫ F.map q₀)
  rw [← Category.assoc, hn v, Category.assoc, ← F.map_comp,
    ← Category.assoc, hn w, Category.assoc, ← F.map_comp, ht']

end Coefficients

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CoverCoequalizer
