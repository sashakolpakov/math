import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedGroupParameters
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedCoefficientMorphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.Comparisons
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedDiagramTransport

/-! # Pointed Group Family -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedGroupFamily.Coefficients

noncomputable section

section

/-! Construct the full pointed group-family diagram over finite
coefficients, retaining the fixed arithmetic source and the actual complex
source map. No family or map model is supplied as an existence assumption. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

structure PointedGroupCoefficientFamily
    (X : Over (Spec (.of R))) (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (A : Over (Spec (.of K))) [GrpObj A]
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ⟶ A)
    (m : ℕ) where
  coefficients : Finset K
  target : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K coefficients)
  group : GrpObj target
  commutative : letI := group; IsCommMonObj target
  smooth : Smooth target.hom
  proper : IsProper target.hom
  embedding : target ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K coefficients) m
  closedImmersion : IsClosedImmersion embedding.left
  map : (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K coefficients)).obj X ⟶ target
  pointed : letI := group
    Section.Comparisons.mappedSection (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K coefficients)) x₀ ≫ map = 1
  sourceIso : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K coefficients)).obj
      ((Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K coefficients)).obj X) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X
  targetIso : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K coefficients)).obj target ≅ A
  targetIso_group : letI := group
    letI : GrpObj ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K coefficients)).obj target) :=
      Functor.grpObjObj (F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K coefficients)) (G := target)
    IsMonHom targetIso.hom
  sourcePoint : Section.Comparisons.mappedSection (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K coefficients))
      (Section.Comparisons.mappedSection (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K coefficients)) x₀) ≫ sourceIso.hom =
    Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))) x₀
  comparison : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K coefficients)).map map ≫ targetIso.hom =
    sourceIso.hom ≫ a

def fixedEnlargementComparison {s t : Finset K} (h : s ⊆ t) :
    Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s) ⋙ Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) ≅
      Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t) :=
  Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
    (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t) (Fixed.CoefficientModels.Coefficients.coefficient_parameterBaseMap R K h)

theorem fixedSourceComparison_point (s : Finset K) (X : Over (Spec (.of R)))
    (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X) :
    Section.Comparisons.mappedSection (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s))
        (Section.Comparisons.mappedSection (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)) x₀) ≫
      ((Fixed.CoefficientModels.Coefficients.fixedSourceComparison R K s).app X).hom =
      Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))) x₀ := by
  exact Section.Comparisons.mappedSection_comp_naturality
    (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)) (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s))
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (Fixed.CoefficientModels.Coefficients.fixedSourceComparison R K s).hom x₀

theorem fixedEnlargementComparison_point {s t : Finset K} (h : s ⊆ t)
    (X : Over (Spec (.of R))) (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X) :
    Section.Comparisons.mappedSection (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h))
        (Section.Comparisons.mappedSection (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)) x₀) ≫
      ((fixedEnlargementComparison R K h).app X).hom =
      Section.Comparisons.mappedSection (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)) x₀ := by
  exact Section.Comparisons.mappedSection_comp_naturality
    (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)) (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h))
    (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)) (fixedEnlargementComparison R K h).hom x₀

theorem fixedEnlargementComparison_inv_point {s t : Finset K} (h : s ⊆ t)
    (X : Over (Spec (.of R))) (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X) :
    Section.Comparisons.mappedSection (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)) x₀ ≫
      ((fixedEnlargementComparison R K h).app X).inv =
      Section.Comparisons.mappedSection (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h))
        (Section.Comparisons.mappedSection (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)) x₀) := by
  rw [← fixedEnlargementComparison_point R K h X x₀, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

def familySourceIso {s t : Finset K} (h : s ⊆ t) (X : Over (Spec (.of R))) :
    (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).obj
        ((Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)).obj X) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X :=
  (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).mapIso
      ((fixedEnlargementComparison R K h).app X).symm ≪≫
    (Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h).app
      ((Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X) ≪≫
    (Fixed.CoefficientModels.Coefficients.fixedSourceComparison R K s).app X

theorem familySourceIso_point {s t : Finset K} (h : s ⊆ t)
    (X : Over (Spec (.of R))) (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X) :
    Section.Comparisons.mappedSection (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t))
        (Section.Comparisons.mappedSection (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)) x₀) ≫
      (familySourceIso R K h X).hom =
      Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))) x₀ := by
  let P := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)
  let H := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let Q := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)
  let T := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)
  let c := Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h
  let k := (fixedEnlargementComparison R K h).app X
  let e := (Fixed.CoefficientModels.Coefficients.fixedSourceComparison R K s).app X
  exact PointedDiagramTransport.section_comparison_change_source F G H c (M := P.obj X) (U := T.obj X) (Z := Q.obj X)
    (Section.Comparisons.mappedSection P x₀) (Section.Comparisons.mappedSection T x₀) (Section.Comparisons.mappedSection Q x₀) k e
    (fixedEnlargementComparison_inv_point R K h X x₀) (fixedSourceComparison_point R K s X x₀)

end

section

/-! Assemble a pointed model diagram at an enlarged coefficient stage,
retaining the actual fixed source, point and generic morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

theorem pointed_group_family_of_enlarged_map
    (X : Over (Spec (.of R))) (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (A : Over (Spec (.of K))) [GrpObj A]
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ⟶ A)
    (m : ℕ) (s : Finset K) (Y : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s))
    [GrpObj Y] [IsCommMonObj Y] [Smooth Y.hom] [IsProper Y.hom]
    (iY : Y ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) m) [IsClosedImmersion iY.left]
    (eY : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj Y ≅ A) [IsMonHom eY.hom]
    (t : Finset K) (h : s ⊆ t)
    (b : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj
        ((Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X) ⟶
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj Y)
    (hb₀ : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).map
        (Section.Comparisons.mappedSection (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)) x₀) ≫ b =
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).map (1 : 𝟙_ _ ⟶ Y))
    (hb : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).map b ≫
        ((Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h).app Y).hom =
      ((Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h).app
        ((Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X)).hom ≫
        ((Fixed.CoefficientModels.Coefficients.fixedSourceComparison R K s).app X).hom ≫ a ≫ eY.inv) :
    Nonempty (PointedGroupCoefficientFamily R K X x₀ A a m) := by
  let P := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)
  let H := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let Q := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let M := P.obj X
  let eX : H.obj M ≅ Q.obj X := (Fixed.CoefficientModels.Coefficients.fixedSourceComparison R K s).app X
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)
  let T := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)
  let N := F.obj Y
  let groupN : GrpObj N := Functor.grpObjObj (F := F) (G := Y)
  let c := Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h
  let k : F.obj M ≅ T.obj X := (fixedEnlargementComparison R K h).app X
  have hkinv : Section.Comparisons.mappedSection T x₀ ≫ k.inv = Section.Comparisons.mappedSection F (Section.Comparisons.mappedSection P x₀) :=
    fixedEnlargementComparison_inv_point R K h X x₀
  let b' : T.obj X ⟶ N := k.inv ≫ b
  have hb' : Section.Comparisons.mappedSection T x₀ ≫ b' = 1 := by
    change Section.Comparisons.mappedSection T x₀ ≫ (k.inv ≫ b) = 1
    rw [← Category.assoc, hkinv]
    exact PointedDiagramTransport.mappedSection_eq_one_of_map F (Section.Comparisons.mappedSection P x₀) b hb₀
  let cN : G.obj N ≅ H.obj Y := c.app Y
  let eN : G.obj N ≅ A := cN ≪≫ eY
  let eM : G.obj (T.obj X) ≅ Q.obj X := familySourceIso R K h X
  have heN : IsMonHom eN.hom := PointedDiagramTransport.iterated_comparison_comp_isMonHom F G H c Y eY
  change G.map b ≫ (c.app Y).hom = (c.app M).hom ≫ eX.hom ≫ a ≫ eY.inv at hb
  have hmap : G.map b' ≫ eN.hom = eM.hom ≫ a := by
    exact PointedDiagramTransport.baseChanged_map_after_comparisons F G H c
      (X := M) (Y := Y) (U := T.obj X) (V := Q.obj X) (W := A) k eX eY b a hb
  have hpoint : Section.Comparisons.mappedSection G (Section.Comparisons.mappedSection T x₀) ≫ eM.hom = Section.Comparisons.mappedSection Q x₀ :=
    familySourceIso_point R K h X x₀
  let φ := ((ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram R K).map (homOfLE h)).hom
  let eP : F.obj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) m) ≅
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t) m := (Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso φ m).symm
  have : IsIso eP.hom.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K t)).mapIso eP).isIso_hom
  have : IsClosedImmersion (F.map iY).left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) iY).flip
      (inferInstanceAs (IsClosedImmersion iY.left))
  have : IsClosedImmersion eP.hom.left := inferInstance
  have hclosed : IsClosedImmersion ((F.map iY).left ≫ eP.hom.left) :=
    IsClosedImmersion.comp (F.map iY).left eP.hom.left
  exact ⟨{
    coefficients := t
    target := N
    group := groupN
    commutative := inferInstance
    smooth := inferInstanceAs (Smooth (pullback.snd Y.hom _))
    proper := inferInstanceAs (IsProper (pullback.snd Y.hom _))
    embedding := F.map iY ≫ eP.hom
    closedImmersion := hclosed
    map := b'
    pointed := hb'
    sourceIso := eM
    targetIso := eN
    targetIso_group := heN
    sourcePoint := hpoint
    comparison := hmap }⟩

end

/-! Construct the full pointed projective group family with fixed source,
using the constructed coefficient target and descended pointed map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

theorem pointed_group_coefficient_family_exists [IsNoetherianRing R]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsProper X.hom]
    (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A] [Smooth A.hom]
    (m : ℕ) (i : A ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K m) [IsClosedImmersion i.left]
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ⟶ A)
    (ha : Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))) x₀ ≫ a = 1) :
    Nonempty (PointedGroupCoefficientFamily R K X x₀ A a m) := by
  obtain ⟨D, groupD, hsD, hpD, hcD, heD⟩ := EmbeddedGroupParameters.Coefficients.smooth_projective_group_coefficient_model R K A m i
  let s := D.toModel.coefficients
  let P := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)
  let H := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let Q := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let M := P.obj X
  let := groupD
  have : IsCommMonObj D.toModel.model := hcD
  have : Smooth D.toModel.model.hom := hsD
  have : IsProper D.toModel.model.hom := hpD
  have : Smooth M.hom := inferInstanceAs (Smooth (pullback.snd X.hom _))
  have : IsProper M.hom := inferInstanceAs (IsProper (pullback.snd X.hom _))
  let eX : H.obj M ≅ Q.obj X := (Fixed.CoefficientModels.Coefficients.fixedSourceComparison R K s).app X
  have hsource : Section.Comparisons.mappedSection H (Section.Comparisons.mappedSection P x₀) ≫ eX.hom = Section.Comparisons.mappedSection Q x₀ :=
    fixedSourceComparison_point R K s X x₀
  have : IsMonHom D.toModel.genericIso.hom := heD
  have : IsMonHom D.toModel.genericIso.inv := inferInstance
  let a₀ : H.obj M ⟶ H.obj D.toModel.model := eX.hom ≫ a ≫ D.toModel.genericIso.inv
  have ha₀ : H.map (Section.Comparisons.mappedSection P x₀) ≫ a₀ = H.map (1 : 𝟙_ _ ⟶ D.toModel.model) := by
    apply (cancel_epi (Functor.LaxMonoidal.ε H)).mp
    change Section.Comparisons.mappedSection H (Section.Comparisons.mappedSection P x₀) ≫ a₀ = Section.Comparisons.mappedSection H (1 : 𝟙_ _ ⟶ D.toModel.model)
    rw [Section.Comparisons.mappedSection_one]
    dsimp only [a₀]
    rw [← Category.assoc, hsource, ← Category.assoc, ha, MonObj.one_comp]
  obtain ⟨t, h, b, hb₀, hb⟩ := PointedCoefficientMorphisms.Coefficients.pointed_generic_morphism_descends M D.toModel.model
    (Section.Comparisons.mappedSection P x₀) 1 a₀ ha₀
  have : IsClosedImmersion D.embedding.left := D.closedImmersion
  exact pointed_group_family_of_enlarged_map R K X x₀ A a m s D.toModel.model
    D.embedding D.toModel.genericIso t h b hb₀ hb

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedGroupFamily.Coefficients
