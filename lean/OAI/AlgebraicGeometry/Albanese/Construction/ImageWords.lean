import OAI.AlgebraicGeometry.Albanese.Construction.Smooth
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

/-! # Image Words -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.ImageWords

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

/-- The algebraic morphism giving the difference of two image points. -/
def differenceMap (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) : X.toOver ⊗ X.toOver ⟶ A.toOver :=
  (fst _ _ ≫ f) / (snd _ _ ≫ f)

@[simp]
theorem diagonal_difference (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) (x : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    lift x x ≫ differenceMap X A f = 1 := by
  simp [differenceMap, GrpObj.comp_div]

/-- The domain of the morphism summing `n` point differences. -/
abbrev wordDomain (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : ℕ → Over Foundations.Scheme.ProjectiveSpace.complexBase
  | 0 => Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
  | n + 1 => wordDomain X n ⊗ (X.toOver ⊗ X.toOver)

instance wordDomain_smooth (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    Smooth (ImageWords.wordDomain X n).hom := by
  have : Smooth X.toOver.hom := X.smooth
  induction n with
  | zero => change Smooth (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase); infer_instance
  | succ n ih =>
    change Smooth (ImageWords.wordDomain X n ⊗ (X.toOver ⊗ X.toOver)).hom
    dsimp
    infer_instance

instance wordDomain_proper (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    IsProper (ImageWords.wordDomain X n).hom := by
  have : IsProper X.toOver.hom := X.projective.isProper
  induction n with
  | zero => change IsProper (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase); infer_instance
  | succ n ih =>
    change IsProper (ImageWords.wordDomain X n ⊗ (X.toOver ⊗ X.toOver)).hom
    dsimp
    infer_instance

instance wordDomain_integral (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (n : ℕ) : IsIntegral (ImageWords.wordDomain X n).left := by
  have : IsIntegral X.toOver.left := Construction.Smooth.connected_presentation_integral X
  have : Smooth X.toOver.hom := X.smooth
  have : IsIntegral (X.toOver ⊗ X.toOver).left :=
    Construction.Smooth.smooth_tensor_integral X.toOver X.toOver
  have : Smooth (X.toOver ⊗ X.toOver).hom := by dsimp; infer_instance
  induction n with
  | zero => change IsIntegral Foundations.Scheme.ProjectiveSpace.complexBase; infer_instance
  | succ n ih => exact Construction.Smooth.smooth_tensor_integral (ImageWords.wordDomain X n) (X.toOver ⊗ X.toOver)

/-- Sum of `n` image-point differences as an actual algebraic morphism. -/
def wordMap (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) : (n : ℕ) → ImageWords.wordDomain X n ⟶ A.toOver
  | 0 => 1
  | n + 1 =>
    (fst _ _ ≫ wordMap X A f n) * (snd _ _ ≫ differenceMap X A f)

/-- Appending a diagonal pair appends a zero point difference. -/
def wordInclusion (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (n : ℕ) :
    ImageWords.wordDomain X n ⟶ ImageWords.wordDomain X (n + 1) :=
  lift (𝟙 _) (toUnit _ ≫ lift x₀ x₀)

@[simp]
theorem wordInclusion_map (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) (n : ℕ) :
    wordInclusion X x₀ n ≫ ImageWords.wordMap X A f (n + 1) = ImageWords.wordMap X A f n := by
  change wordInclusion X x₀ n ≫
    ((fst _ _ ≫ ImageWords.wordMap X A f n) * (snd _ _ ≫ differenceMap X A f)) = _
  rw [MonObj.comp_mul]
  simp only [← Category.assoc, wordInclusion, lift_fst, lift_snd, Category.id_comp]
  rw [Category.assoc, diagonal_difference]
  simp

instance wordMap_proper (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) (n : ℕ) : IsProper (ImageWords.wordMap X A f n).left := by
  have : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
  have : IsProper ((ImageWords.wordMap X A f n).left ≫ A.toOver.hom) := by
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp _ A.toOver.hom

/-- The image of each finite-word morphism is an irreducible closed support. -/
def wordSupport (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [ConnectedSpace X.carrier]
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) (n : ℕ) :
    IrreducibleCloseds A.carrier where
  carrier := Set.range (ImageWords.wordMap X A f n).left
  isIrreducible' := by
    change IsIrreducible (Set.range (ImageWords.wordMap X A f n).left : Set A.toOver.left)
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ _).image (ImageWords.wordMap X A f n).left
        (ImageWords.wordMap X A f n).left.continuous.continuousOn)
  isClosed' := (ImageWords.wordMap X A f n).left.isClosedMap.isClosed_range

theorem wordSupport_mono (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [ConnectedSpace X.carrier]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) : Monotone (wordSupport X A f) := by
  apply monotone_nat_of_le_succ
  intro n z hz
  obtain ⟨x, rfl⟩ := hz
  refine ⟨(wordInclusion X x₀ n).left x, ?_⟩
  change ((wordInclusion X x₀ n ≫ ImageWords.wordMap X A f (n + 1)).left) x = _
  rw [wordInclusion_map]

/-- The finite-word images have two consecutive equal members before their
dimensions could exceed the dimension of the ambient abelian variety. -/
theorem exists_wordSupport_eq_succ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver) :
    ∃ n ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap,
      wordSupport X A f n = wordSupport X A f (n + 1) := by
  classical
  let D := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap
  let d (n : ℕ) := Foundations.Scheme.SupportDimension.supportTranscendenceDimension (wordSupport X A f n) A.variety.structureMap
  by_contra h
  have hne (n : ℕ) (hn : n ≤ D) : wordSupport X A f n ≠ wordSupport X A f (n + 1) := by
    intro heq
    exact h ⟨n, hn, heq⟩
  have hstep (n : ℕ) (hn : n ≤ D) : d n < d (n + 1) :=
    Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt _ _ A.variety.structureMap
      (lt_of_le_of_ne (wordSupport_mono X x₀ A f (Nat.le_succ n)) (hne n hn))
  have hgrowth : ∀ n, n ≤ D + 1 → n ≤ d n := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hnext := hstep n (by omega)
      omega
  have hlower := hgrowth (D + 1) (Nat.le_refl _)
  have hupper : d (D + 1) ≤ D :=
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le (wordSupport X A f (D + 1)) A.variety.structureMap
  omega

end

end OAI.AlgebraicGeometry.Albanese.Construction.ImageWords
