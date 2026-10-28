import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLifts
import OAI.AlgebraicGeometry.Albanese.Construction.FiniteRefinements

/-! # Albanese Isogeny -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseIsogeny

noncomputable section

/-! A generating specialization of the same dimension gives an actual
finite etale isogeny from the complex Albanese. The original Albanese map
is its unique pointed lift. This is the geometric isogeny step in arithmetic
descent, without assuming that the Albanese has a number-field model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Pointwise

theorem generates_of_surjective_word (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver)
    (n : ℕ) (hn : Surjective (Albanese.Construction.ImageWords.wordMap X A a n).left) : Albanese.Construction.GeneratedClosed.Generates X A a := by
  have : LocallyOfFiniteType A.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType A.variety.structureMap)
  apply le_antisymm le_top
  intro z _
  have hz : z ∈ Albanese.Construction.WordPoints.wordPointImage X A a n :=
    (Albanese.Construction.ClosedPoints.pointMap_range_iff (Albanese.Construction.ImageWords.wordDomain X n) A.toOver (Albanese.Construction.ImageWords.wordMap X A a n) z).mpr
      (hn.surj (z.left (IsLocalRing.closedPoint ℂ)))
  rw [Albanese.Construction.WordPoints.wordPointImage_eq_pow] at hz
  exact Subgroup.pow_subset Subgroup.subset_closure hz

/-- A pointed generating map to an abelian variety of Albanese dimension
constructs a finite etale surjective factor. The Albanese map is the unique
pointed lift through that factor. -/
theorem albanese_finite_etale_factor
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [ConnectedSpace X.carrier]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (b : X.toOver ⟶ B.toOver)
    (ha : Albanese.IsAlbaneseMap X x₀ A a) (hb₀ : x₀ ≫ b = 1)
    (n : ℕ) (hn : Surjective (Albanese.Construction.ImageWords.wordMap X B b n).left)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap) :
    ∃ φ : A.toOver ⟶ B.toOver,
      IsMonHom φ ∧ a ≫ φ = b ∧ IsFinite φ.left ∧ Etale φ.left ∧ Surjective φ.left ∧
      ∀ a' : X.toOver ⟶ A.toOver, x₀ ≫ a' = 1 → a' ≫ φ = b → a' = a := by
  obtain ⟨φ, ⟨hφgroup, hφ⟩, _⟩ := ha.2 B b hb₀
  let := hφgroup
  have hgen := generates_of_surjective_word X B b n hn
  have hfinite : IsFinite φ.left := Albanese.Construction.FiniteRefinements.refinement_finite X A B a b φ hφ hgen hd
  have hetale : Etale φ.left := Albanese.Construction.FiniteRefinements.refinement_etale X A B a b φ hφ hgen hd
  have hsurj : Surjective φ.left := Albanese.Construction.GeneratedClosed.refinement_surjective X A B a b φ hφ hgen
  refine ⟨φ, hφgroup, hφ, hfinite, hetale, hsurj, ?_⟩
  intro a' ha' hφ'
  have : ConnectedSpace X.toOver.left := inferInstanceAs (ConnectedSpace X.carrier)
  have : Nonempty (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).left := ⟨IsLocalRing.closedPoint ℂ⟩
  apply Over.OverMorphism.ext
  exact PointedLifts.pointed_unramified_lifts_unique φ.left a'.left a.left
    (congrArg Over.Hom.left (hφ'.trans hφ.symm)) x₀.left
    (congrArg Over.Hom.left (ha'.trans ha.1.symm))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseIsogeny
