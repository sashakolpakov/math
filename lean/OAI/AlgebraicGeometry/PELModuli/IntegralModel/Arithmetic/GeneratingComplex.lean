import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GeneratingTarget
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedAbelianVarieties
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexComparison

/-! # Generating Complex -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic

noncomputable section

/-! The arithmetic generating target supplies a native complex abelian
variety, with a pointed generating map and exact Albanese dimension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [Field R] [NumberField R] [Algebra R ℂ]
  {B : Base.ArithmeticBaseExtension R (algebraMap R ℂ)}
  {X : Over (Spec (.of R))} {x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X}
  {A : Over (Spec (.of ℂ))} {n m : ℕ} (T : GeneratingTarget.ArithmeticGeneratingTarget B X x₀ A n m)

def GeneratingTarget.ArithmeticGeneratingTarget.complexTarget : Over (Spec (.of ℂ)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj T.target.toOver

instance GeneratingTarget.ArithmeticGeneratingTarget.complexTarget_group : GrpObj T.complexTarget := Functor.grpObjObj
  (F := Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))) (G := T.target.toOver)

instance GeneratingTarget.ArithmeticGeneratingTarget.complexTarget_commutative : IsCommMonObj T.complexTarget :=
  inferInstanceAs (IsCommMonObj
    ((Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj T.target.toOver))

instance GeneratingTarget.ArithmeticGeneratingTarget.complexTarget_smooth : Smooth T.complexTarget.hom := inferInstanceAs
  (Smooth (pullback.snd T.target.toOver.hom (Spec.map (CommRingCat.ofHom B.embedding))))

instance GeneratingTarget.ArithmeticGeneratingTarget.complexTarget_proper : IsProper T.complexTarget.hom := inferInstanceAs
  (IsProper (pullback.snd T.target.toOver.hom (Spec.map (CommRingCat.ofHom B.embedding))))

instance GeneratingTarget.ArithmeticGeneratingTarget.complexTarget_connected : GeometricallyConnected T.complexTarget.hom := inferInstanceAs
  (GeometricallyConnected (pullback.snd T.target.toOver.hom (Spec.map (CommRingCat.ofHom B.embedding))))

def GeneratingTarget.ArithmeticGeneratingTarget.complexEmbedding : T.complexTarget ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ m :=
  (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).map T.embedding ≫
    (Generating.affineProjectiveBaseChangeAlong (Spec.map (CommRingCat.ofHom B.embedding)) m).hom

instance GeneratingTarget.ArithmeticGeneratingTarget.complexEmbedding_closed : IsClosedImmersion T.complexEmbedding.left := by
  let ψ := Spec.map (CommRingCat.ofHom B.embedding)
  let F := Over.pullback ψ
  let e := Generating.affineProjectiveBaseChangeAlong ψ m
  have : IsIso e.hom.left := ((Over.forget (Spec (.of ℂ))).mapIso e).isIso_hom
  have : IsClosedImmersion (F.map T.embedding).left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback ψ T.embedding).flip T.closedImmersion
  change IsClosedImmersion ((F.map T.embedding).left ≫ e.hom.left)
  infer_instance

def GeneratingTarget.ArithmeticGeneratingTarget.complexVariety : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety :=
  EmbeddedAbelianVarieties.embeddedAbelianVariety T.complexTarget m T.complexEmbedding

def GeneratingTarget.ArithmeticGeneratingTarget.complexMap : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶
    T.complexTarget :=
  ((ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B).app X).inv ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).map T.map

theorem GeneratingTarget.ArithmeticGeneratingTarget.complexMap_pointed :
    Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀ ≫
      T.complexMap = 1 := by
  let P := Over.pullback B.fieldExtension
  let F := Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))
  let H := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  let c := ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B
  let e : F.obj (P.obj X) ≅ H.obj X := c.app X
  have hx : Section.Comparisons.mappedSection F (Section.Comparisons.mappedSection P x₀) ≫ e.hom = Section.Comparisons.mappedSection H x₀ :=
    Section.Comparisons.mappedSection_comp_naturality P F H c.hom x₀
  exact Generating.pointed_map_after_source_iso F (X := P.obj X) (Y := T.target.toOver) (U := H.obj X)
    (Section.Comparisons.mappedSection P x₀) (Section.Comparisons.mappedSection H x₀) e T.map hx T.pointed

theorem GeneratingTarget.ArithmeticGeneratingTarget.complexMap_word_surjective : Surjective (Words.DifferenceWords.map T.complexMap n).left := by
  let ψ := Spec.map (CommRingCat.ofHom B.embedding)
  let P := Over.pullback B.fieldExtension
  let F := Over.pullback ψ
  let H := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  let e : F.obj (P.obj X) ≅ H.obj X := (ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B).app X
  have hw : Surjective (F.map (Words.DifferenceWords.map T.map n)).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square ψ (Words.DifferenceWords.map T.map n)) T.word_surjective
  have hwF : Surjective (Words.DifferenceWords.map (F.map T.map) n).left :=
    Generating.DifferenceWords.surjective_word_of_baseChange ψ T.map n hw
  have : IsMonHom (Iso.refl T.complexTarget).hom := inferInstanceAs (IsMonHom (𝟙 T.complexTarget))
  exact Generating.DifferenceWords.surjective_word_of_comparison
    (X := H.obj X) (A := T.complexTarget) (Y := F.obj (P.obj X)) (B := T.complexTarget)
    T.complexMap (F.map T.map) e.symm (Iso.refl T.complexTarget)
    (by simp only [GeneratingTarget.ArithmeticGeneratingTarget.complexMap, e, F, ψ, Iso.refl_hom, Category.comp_id, Iso.symm_hom]) n hwF

omit T in
theorem GeneratingTarget.ArithmeticGeneratingTarget.complexVariety_dimension
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (T : GeneratingTarget.ArithmeticGeneratingTarget B X x₀ A.toOver n m) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension T.complexVariety.variety.structureMap := by
  have : Smooth A.toOver.hom := A.variety.presentation.smooth
  have : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
  have : IsIntegral A.toOver.left := A.variety.property
  have : GeometricallyConnected A.toOver.hom :=
    ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents.Construction.integral_geometricallyConnected_over_algClosed A.toOver.hom
  have hA := Group.FamilyDimension.group_krullDim_eq_transcendenceDimension A.toOver
  have hY := EmbeddedAbelianVarieties.embeddedAbelianVariety_dimension T.complexTarget m T.complexEmbedding
  have hd : (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap : WithBot ℕ∞) =
      (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension T.complexVariety.variety.structureMap : WithBot ℕ∞) :=
    hA.symm.trans (T.dimension.trans hY)
  exact_mod_cast hd

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic
