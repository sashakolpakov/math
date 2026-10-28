import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GeneratingComplex
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstructionWordComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseIsogeny

/-! # Albanese Arithmetic Isogeny -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseArithmeticIsogeny

noncomputable section

/-! Construct an arithmetic target and a finite étale isogeny to it from
the specified complex Albanese. No arithmetic abelian model is an input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [Field R] [NumberField R] [Algebra R ℂ]

def complexSourcePresentation (X : Over (Spec (.of R))) [Smooth X.hom]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom) :
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).left
  structureMap := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom
  projective := P
  smooth := inferInstanceAs
    (Smooth (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))))

theorem albanese_arithmetic_isogeny_target
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A.toOver)
    (ha : Albanese.IsAlbaneseMap (complexSourcePresentation X P)
      (Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀) A a)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension R (algebraMap R ℂ)) (n : ℕ)
      (T : Arithmetic.GeneratingTarget.ArithmeticGeneratingTarget B X x₀ A.toOver n A.variety.presentation.ambientDimension)
      (φ : A.toOver ⟶ T.complexTarget),
      B.denominator = N ∧ 0 < n ∧ IsMonHom φ ∧ a ≫ φ = T.complexMap ∧
        IsFinite φ.left ∧ Etale φ.left ∧ Surjective φ.left := by
  let H := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  let V := complexSourcePresentation X P
  let x : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ V.toOver := Section.Comparisons.mappedSection H x₀
  have : GeometricallyConnected (H.obj X).hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))))
  have hconnected : ConnectedSpace (H.obj X).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (H.obj X).hom
  have : ConnectedSpace V.carrier := hconnected
  have : Smooth A.toOver.hom := A.variety.presentation.smooth
  obtain ⟨n, hn, hw⟩ := Albanese.albanese_finite_word_surjective V x A a ha
  have hword : Surjective (Words.DifferenceWords.map a n).left :=
    ConstructionWordComparison.DifferenceWords.word_surjective_of_e07 V A a n hw
  obtain ⟨B, hB, ⟨T⟩⟩ := Arithmetic.GeneratingTarget.arithmetic_generating_target_exists X x₀ A.toOver
    (EmbeddedAbelianVarieties.abelianVariety_projectiveEmbedding A) a ha.1 n hword N hN
  have hwT : Surjective (Albanese.Construction.ImageWords.wordMap V T.complexVariety T.complexMap n).left :=
    ConstructionWordComparison.DifferenceWords.e07_surjective_of_word V T.complexVariety T.complexMap n T.complexMap_word_surjective
  obtain ⟨φ, hφ, hmap, hfinite, hetale, hsurj, _⟩ := AlbaneseIsogeny.albanese_finite_etale_factor
    V x A T.complexVariety a T.complexMap ha T.complexMap_pointed n hwT
      (Arithmetic.GeneratingTarget.ArithmeticGeneratingTarget.complexVariety_dimension A T)
  exact ⟨B, n, T, φ, hB, hn, hφ, hmap, hfinite, hetale, hsurj⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseArithmeticIsogeny
