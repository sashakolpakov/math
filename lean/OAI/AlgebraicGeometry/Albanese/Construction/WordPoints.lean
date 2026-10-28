import OAI.AlgebraicGeometry.Albanese.Construction.ImageWords
import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints
import OAI.AlgebraicGeometry.Albanese.Construction.SetPowers

/-! # Word Points -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.WordPoints

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Pointwise

/-- Rational points reached by the finite-word morphism. -/
def wordPointImage (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) (n : ℕ) :
    Set (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver) :=
  Set.range (fun p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ ImageWords.wordDomain X n => p ≫ ImageWords.wordMap X A f n)

/-- Rational point differences reached by the two-point morphism. -/
def differencePointImage (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) : Set (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver) :=
  Set.range (fun p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver ⊗ X.toOver =>
    p ≫ ImageWords.differenceMap X A f)

theorem one_mem_differencePointImage (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) : 1 ∈ differencePointImage X A f :=
  ⟨lift x₀ x₀, ImageWords.diagonal_difference X A f x₀⟩

theorem differencePointImage_inv_mem (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver)
    {z : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver}
    (hz : z ∈ differencePointImage X A f) : z⁻¹ ∈ differencePointImage X A f := by
  obtain ⟨p, rfl⟩ := hz
  refine ⟨p ≫ (β_ X.toOver X.toOver).hom, ?_⟩
  simp [ImageWords.differenceMap, GrpObj.comp_div, Category.assoc, inv_div]

theorem wordPointImage_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) :
    wordPointImage X A f 0 = 1 := by
  have : Nonempty (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ ImageWords.wordDomain X 0) := ⟨𝟙 _⟩
  ext z
  simp [wordPointImage, ImageWords.wordMap]

theorem wordPointImage_succ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) (n : ℕ) :
    wordPointImage X A f (n + 1) = wordPointImage X A f n * differencePointImage X A f := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨(p ≫ fst _ _) ≫ ImageWords.wordMap X A f n, ⟨p ≫ fst _ _, rfl⟩,
      (p ≫ snd _ _) ≫ ImageWords.differenceMap X A f, ⟨p ≫ snd _ _, rfl⟩, ?_⟩
    simp [ImageWords.wordMap, MonObj.comp_mul, Category.assoc]
  · rintro ⟨x, ⟨p, rfl⟩, y, ⟨q, rfl⟩, rfl⟩
    refine ⟨lift p q, ?_⟩
    simp [ImageWords.wordMap, MonObj.comp_mul]

theorem wordPointImage_eq_pow (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) (n : ℕ) :
    wordPointImage X A f n = differencePointImage X A f ^ n := by
  induction n with
  | zero => simpa using wordPointImage_zero X A f
  | succ n ih => rw [wordPointImage_succ, ih, pow_succ]

theorem mem_wordPointImage_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) (n : ℕ)
    (z : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver) :
    z ∈ wordPointImage X A f n ↔
      z.left (IsLocalRing.closedPoint ℂ) ∈ ImageWords.wordSupport X A f n := by
  have : LocallyOfFiniteType A.toOver.hom := by
    change LocallyOfFiniteType A.variety.structureMap
    infer_instance
  exact ClosedPoints.pointMap_range_iff (ImageWords.wordDomain X n) A.toOver (ImageWords.wordMap X A f n) z

theorem exists_differencePointImage_pow_eq_succ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) :
    ∃ n ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap,
      differencePointImage X A f ^ n = differencePointImage X A f ^ (n + 1) := by
  obtain ⟨n, hn, heq⟩ := ImageWords.exists_wordSupport_eq_succ X x₀ A f
  refine ⟨n, hn, ?_⟩
  rw [← wordPointImage_eq_pow, ← wordPointImage_eq_pow]
  ext z
  simp only [mem_wordPointImage_iff, heq]

/-- The subgroup generated by point differences is itself the complex-point
set of an irreducible closed algebraic support in the target abelian variety. -/
theorem exists_generated_point_support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) :
    ∃ Z : TopologicalSpace.IrreducibleCloseds A.carrier,
      ∀ z : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver,
        z.left (IsLocalRing.closedPoint ℂ) ∈ Z ↔
          z ∈ Subgroup.closure (differencePointImage X A f) := by
  obtain ⟨n, _, hn⟩ := exists_differencePointImage_pow_eq_succ X x₀ A f
  let S := differencePointImage X A f
  have h1 : 1 ∈ S := one_mem_differencePointImage X x₀ A f
  have hinv : ∀ z ∈ S, z⁻¹ ∈ S := fun z hz => differencePointImage_inv_mem X A f hz
  have hclosure := SetPowers.stablePowerSubgroup_eq_closure S h1 hinv n hn
  refine ⟨ImageWords.wordSupport X A f n, fun z => ?_⟩
  rw [← mem_wordPointImage_iff, wordPointImage_eq_pow, ← hclosure]
  rfl

end

end OAI.AlgebraicGeometry.Albanese.Construction.WordPoints
