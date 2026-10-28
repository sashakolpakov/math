import OAI.AlgebraicGeometry.Albanese.Construction.GeneratedClosed

/-! # Generating Words -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.GeneratingWords

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Pointwise

/-- In a generated target, every point is a sum of at most `dim A` point
differences. The bound follows from strict dimension growth before stabilization. -/
theorem generating_wordPointImage_eq_univ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (ha : GeneratedClosed.Generates X A a)
    (m : ℕ) (hm : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap ≤ m) :
    WordPoints.wordPointImage X A a m = Set.univ := by
  obtain ⟨n, hn, hstable⟩ := WordPoints.exists_differencePointImage_pow_eq_succ X x₀ A a
  let S := WordPoints.differencePointImage X A a
  have h1 : 1 ∈ S := WordPoints.one_mem_differencePointImage X x₀ A a
  have hinv : ∀ z ∈ S, z⁻¹ ∈ S := fun z hz => WordPoints.differencePointImage_inv_mem X A a hz
  have hclosure := SetPowers.stablePowerSubgroup_eq_closure S h1 hinv n hstable
  have htop : S ^ n = Set.univ := by
    have hgroup : SetPowers.stablePowerSubgroup S h1 hinv n hstable = ⊤ := hclosure.trans ha
    exact congrArg (fun H : Subgroup (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver) =>
      (H : Set (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver))) hgroup
  rw [WordPoints.wordPointImage_eq_pow]
  change S ^ m = Set.univ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (hn.trans hm)
  rw [SetPowers.setPow_stable_add S n hstable, htop]

/-- The dimension bound gives a surjection on complex points from one fixed
finite product of the source. -/
theorem generating_word_point_surjective (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (ha : GeneratedClosed.Generates X A a)
    (m : ℕ) (hm : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap ≤ m) :
    Function.Surjective (fun p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ ImageWords.wordDomain X m =>
      p ≫ ImageWords.wordMap X A a m) := by
  intro q
  have hq : q ∈ WordPoints.wordPointImage X A a m := by
    rw [generating_wordPointImage_eq_univ X x₀ A a ha m hm]
    trivial
  exact hq

/-- The same word morphism is surjective on the actual scheme, including
nonclosed points. -/
theorem generating_word_surjective (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (ha : GeneratedClosed.Generates X A a)
    (m : ℕ) (hm : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap ≤ m) :
    Surjective (ImageWords.wordMap X A a m).left := by
  have : LocallyOfFiniteType A.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType A.variety.structureMap)
  let w := ImageWords.wordMap X A a m
  have hfull : Set.range (𝟙 A.toOver : A.toOver ⟶ A.toOver).left ⊆ Set.range w.left := by
    apply ReducedFactor.range_subset_closed_of_points A.toOver A.toOver (𝟙 A.toOver)
      ⟨Set.range w.left, w.left.isClosedMap.isClosed_range⟩
    intro q
    obtain ⟨p, hp⟩ := generating_word_point_surjective X x₀ A a ha m hm q
    refine ⟨p.left (IsLocalRing.closedPoint ℂ), ?_⟩
    exact congrArg (fun r : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver =>
      r.left (IsLocalRing.closedPoint ℂ)) hp
  exact ⟨fun q => hfull ⟨q, rfl⟩⟩

/-- Word morphisms commute with homomorphisms of target abelian varieties. -/
theorem wordMap_comp (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (φ : A.toOver ⟶ B.toOver) [IsMonHom φ] (n : ℕ) :
    ImageWords.wordMap X A a n ≫ φ = ImageWords.wordMap X B (a ≫ φ) n := by
  induction n with
  | zero => simp [ImageWords.wordMap]
  | succ n ih =>
    simp [ImageWords.wordMap, MonObj.mul_comp, Category.assoc, ih, ImageWords.differenceMap, GrpObj.div_comp]

/-- Agreement after a generating source map determines a homomorphism. -/
theorem generating_hom_ext (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (ha : GeneratedClosed.Generates X A a)
    (φ ψ : A.toOver ⟶ B.toOver) [IsMonHom φ] [IsMonHom ψ]
    (h : a ≫ φ = a ≫ ψ) : φ = ψ := by
  have : IsClosedImmersion (𝟙 A.toOver : A.toOver ⟶ A.toOver).left := by
    change IsClosedImmersion (𝟙 A.carrier)
    infer_instance
  apply GeneratedClosed.generated_hom_ext X A A B a a (𝟙 A.toOver) (by simp) _ φ ψ h
  intro q
  rw [ha]
  exact ⟨fun _ => Subgroup.mem_top _, fun _ => ⟨q, by simp⟩⟩

end

end OAI.AlgebraicGeometry.Albanese.Construction.GeneratingWords
