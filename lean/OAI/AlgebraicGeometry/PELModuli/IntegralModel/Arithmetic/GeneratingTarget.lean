import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedFamilySpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Generating
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianQuotient

/-! # Generating Target -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GeneratingTarget

noncomputable section

/-! An actual arithmetic abelian target of the required Albanese dimension,
with a pointed generating map from the native extension of the fixed source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedFamilySpecialization.Coefficients

variable {R : Type} [Field R] [NumberField R] [Algebra R ℂ]

structure ArithmeticGeneratingTarget (B : Base.ArithmeticBaseExtension R (algebraMap R ℂ))
    (X : Over (Spec (.of R))) (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (A : Over (Spec (.of ℂ))) (n m : ℕ) where
  target : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of B.extension.carrier))
  embedding : target.toOver ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace B.extension.carrier m
  closedImmersion : IsClosedImmersion embedding.left
  map : (Over.pullback B.fieldExtension).obj X ⟶ target.toOver
  pointed : Section.Comparisons.mappedSection (Over.pullback B.fieldExtension) x₀ ≫ map = 1
  word_surjective : Surjective (Words.DifferenceWords.map map n).left
  dimension : topologicalKrullDim A.left = topologicalKrullDim
    ((Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj target.toOver).left

theorem arithmetic_generating_target_of_parameter
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X) (A : Over (Spec (.of ℂ))) [GrpObj A]
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A)
    {n m : ℕ} (D : PointedGroupFamily.Coefficients.PointedGroupCoefficientFamily R ℂ X x₀ A a m)
    (B : Base.ArithmeticBaseExtension R (algebraMap R ℂ))
    (p : Over.mk B.fieldExtension ⟶ Fixed.CoefficientModels.Coefficients.coefficientParameter R ℂ D.coefficients)
    (hw : letI := D.group
      Surjective ((Over.pullback p.left).map (Words.DifferenceWords.map D.map n)).left)
    (hd : topologicalKrullDim A.left = topologicalKrullDim ((Over.pullback
      (Spec.map (CommRingCat.ofHom B.embedding) ≫ p.left)).obj D.target).left) :
    Nonempty (ArithmeticGeneratingTarget B X x₀ A n m) := by
  let groupD : GrpObj D.target := D.group
  have : IsCommMonObj D.target := D.commutative
  have : Smooth D.target.hom := D.smooth
  have : IsProper D.target.hom := D.proper
  let u : Spec (.of B.extension.carrier) ⟶ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R ℂ D.coefficients := p.left
  let P : Over (Spec (.of R)) ⥤ Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R ℂ D.coefficients) :=
    Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R ℂ D.coefficients)
  let F : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R ℂ D.coefficients) ⥤ Over (Spec (.of B.extension.carrier)) :=
    Over.pullback u
  let Q : Over (Spec (.of R)) ⥤ Over (Spec (.of B.extension.carrier)) := Over.pullback B.fieldExtension
  let M := P.obj X
  let Y : Over (Spec (.of B.extension.carrier)) := F.obj D.target
  let groupY : GrpObj Y := Functor.grpObjObj (F := F) (G := D.target)
  have : IsCommMonObj Y := inferInstance
  have hsY : Smooth Y.hom := inferInstanceAs (Smooth (pullback.snd D.target.hom u))
  have hpY : IsProper Y.hom := inferInstanceAs (IsProper (pullback.snd D.target.hom u))
  have hpbase : u ≫ Fixed.CoefficientModels.Coefficients.parameterBaseMap R ℂ D.coefficients = B.fieldExtension := p.w
  let c : P ⋙ F ≅ Q := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso
    (Fixed.CoefficientModels.Coefficients.parameterBaseMap R ℂ D.coefficients) u B.fieldExtension hpbase
  let eX : F.obj M ≅ Q.obj X := c.app X
  let b : Q.obj X ⟶ Y := eX.inv ≫ F.map D.map
  have hx : Section.Comparisons.mappedSection F (Section.Comparisons.mappedSection P x₀) ≫ eX.hom = Section.Comparisons.mappedSection Q x₀ :=
    Section.Comparisons.mappedSection_comp_naturality P F Q c.hom x₀
  have hb : Section.Comparisons.mappedSection Q x₀ ≫ b = 1 :=
    Generating.pointed_map_after_source_iso F (X := M) (Y := D.target) (U := Q.obj X)
      (Section.Comparisons.mappedSection P x₀) (Section.Comparisons.mappedSection Q x₀) eX D.map hx D.pointed
  have hwF : Surjective (Words.DifferenceWords.map (F.map D.map) n).left :=
    Generating.DifferenceWords.surjective_word_of_baseChange u (X := M) (A := D.target) D.map n hw
  have : IsMonHom (Iso.refl Y).hom := inferInstanceAs (IsMonHom (𝟙 Y))
  have hwB : Surjective (Words.DifferenceWords.map b n).left :=
    Generating.DifferenceWords.surjective_word_of_comparison (X := Q.obj X) (A := Y) (Y := F.obj M) (B := Y)
      b (F.map D.map) eX.symm (Iso.refl Y)
      (by simp only [b, Iso.refl_hom, Category.comp_id, Iso.symm_hom]) n hwF
  have : Smooth (Q.obj X).hom := inferInstanceAs (Smooth (pullback.snd X.hom B.fieldExtension))
  have : GeometricallyConnected (Q.obj X).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd X.hom B.fieldExtension))
  have hcY : GeometricallyConnected Y.hom := GeneratingFiberConnectedness.DifferenceWords.target_geometricallyConnected b n
  let Y₀ : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of B.extension.carrier)) := {
    toOver := Y
    smooth := hsY
    proper := hpY
    connected := hcY }
  let eP := Generating.affineProjectiveBaseChangeAlong
    (R := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R ℂ D.coefficients) (K := B.extension.carrier) u m
  have : IsIso eP.hom.left := ((Over.forget (Spec (.of B.extension.carrier))).mapIso eP).isIso_hom
  have : IsClosedImmersion (F.map D.embedding).left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback u D.embedding).flip D.closedImmersion
  have : IsClosedImmersion eP.hom.left := inferInstance
  have hi : IsClosedImmersion ((F.map D.embedding).left ≫ eP.hom.left) :=
    IsClosedImmersion.comp (F.map D.embedding).left eP.hom.left
  let ψ := Spec.map (CommRingCat.ofHom B.embedding)
  let eC : (Over.pullback (ψ ≫ u)).obj D.target ≅ (Over.pullback ψ).obj Y :=
    (Over.pullbackComp ψ u).app D.target
  have : IsIso eC.hom.left := ((Over.forget (Spec (.of ℂ))).mapIso eC).isIso_hom
  have heC : topologicalKrullDim ((Over.pullback (ψ ≫ u)).obj D.target).left =
      topologicalKrullDim ((Over.pullback ψ).obj Y).left :=
    eC.hom.left.homeomorph.isHomeomorph.topologicalKrullDim_eq
  exact ⟨{
    target := Y₀
    embedding := F.map D.embedding ≫ eP.hom
    closedImmersion := hi
    map := b
    pointed := hb
    word_surjective := hwB
    dimension := hd.trans heC }⟩

/-- Construct the arithmetic generating target directly from the complex
pointed generating map and its projective embedding. -/
theorem arithmetic_generating_target_exists
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (A : Over (Spec (.of ℂ))) [GrpObj A] [IsCommMonObj A] [Smooth A.hom]
    {m : ℕ} (i : A ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ m) [IsClosedImmersion i.left]
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A)
    (ha : Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀ ≫ a = 1)
    (n : ℕ) (hn : Surjective (Words.DifferenceWords.map a n).left)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ B : Base.ArithmeticBaseExtension R (algebraMap R ℂ),
      B.denominator = N ∧ Nonempty (ArithmeticGeneratingTarget B X x₀ A n m) := by
  obtain ⟨D, B, p, hB, hw, hd⟩ := PointedFamilySpecialization.Coefficients.arithmetic_generating_family_exists X x₀ A a i ha n hn N hN
  exact ⟨B, hB, arithmetic_generating_target_of_parameter X x₀ A a D B p hw hd⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GeneratingTarget
