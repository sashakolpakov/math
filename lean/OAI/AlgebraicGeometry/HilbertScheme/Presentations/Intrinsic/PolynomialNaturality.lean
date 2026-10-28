import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialFamily

/-! # Polynomial Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialNaturality.GradedHilbert

noncomputable section

/-! The actual polynomial closed subschemes, and the bounded native Hilbert
families they define, commute with arbitrary changes of test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}

def nativePolynomialTestMap {T U : Over S} (a : U ⟶ T) (x : T ⟶ M) :
    Over.mk (a ≫ x).left ⟶ Over.mk x.left := Over.homMk a.left rfl

theorem nativePolynomialCoefficientProjection_naturality {T U : Over S} (a : U ⟶ T) (x : T ⟶ M) :
    Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (nativePolynomialTestMap M a x) ≫
      PolynomialCoordinates.GradedHilbert.nativePolynomialCoefficientProjection M x = PolynomialCoordinates.GradedHilbert.nativePolynomialCoefficientProjection M (a ≫ x) := by
  let X := PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n
  let τ := nativePolynomialTestMap M a x
  have h : (prod.map τ (𝟙 X)).left ≫ (prod.snd : Over.mk x.left ⨯ X ⟶ X).left =
      (prod.snd : Over.mk (a ≫ x).left ⨯ X ⟶ X).left := by
    rw [← Over.comp_left, prod.map_snd, Category.comp_id]
  change (prod.map τ (𝟙 X)).left ≫ ((prod.snd : Over.mk x.left ⨯ X ⟶ X).left ≫ pullback.fst _ _) = _
  rw [← Category.assoc, h]
  rfl

variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))

theorem nativePolynomialInclusion_baseChange {T U : Over S} (a : U ⟶ T) (x : T ⟶ M) :
    PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (a ≫ x) ≫
        Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (nativePolynomialTestMap M a x) =
      Relative.PolynomialBaseChange.GradedHilbert.relativePolynomialBaseMap M I a x ≫ PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x := by
  apply PolynomialCoordinates.GradedHilbert.nativePolynomialAmbient_hom_ext M x
  · rw [Category.assoc, ← (Hilbert.Functor.ambient_isPullback (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n)
      (nativePolynomialTestMap M a x)).w, ← Category.assoc, PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection,
      Category.assoc, PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection]
    exact (Relative.PolynomialBaseChange.GradedHilbert.relativePolynomialBaseMap_projection M I a x).symm
  · rw [Category.assoc, nativePolynomialCoefficientProjection_naturality,
      PolynomialCoordinates.GradedHilbert.nativePolynomialInclusion_coefficient, Category.assoc, PolynomialCoordinates.GradedHilbert.nativePolynomialInclusion_coefficient]
    let j : Proj (Graded.Quotient.GradedHilbert.quotientGrading I) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n) := Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I
    have h := congrArg (fun f => f ≫ j) (Relative.PolynomialBaseChange.GradedHilbert.relativePolynomialBaseMap_fst M I a x)
    exact h.symm.trans (Category.assoc _ _ _)

theorem nativePolynomialInclusion_baseChange_isPullback {T U : Over S} (a : U ⟶ T) (x : T ⟶ M) :
    IsPullback (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (a ≫ x)) (Relative.PolynomialBaseChange.GradedHilbert.relativePolynomialBaseMap M I a x)
      (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (nativePolynomialTestMap M a x))
      (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x) := by
  apply IsPullback.of_right _ (nativePolynomialInclusion_baseChange M I a x)
    (Hilbert.Functor.ambient_isPullback (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (nativePolynomialTestMap M a x))
  rw [PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection, PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection]
  exact (Relative.PolynomialBaseChange.GradedHilbert.relativePolynomialBaseMap_isPullback M I a x).flip

theorem nativePolynomialIdeal_baseChange {T U : Over S} (a : U ⟶ T) (x : T ⟶ M) :
    (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (a ≫ x)).ker =
      (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x).ker.comap
        (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (nativePolynomialTestMap M a x)) := by
  let H := nativePolynomialInclusion_baseChange_isPullback M I a x
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

theorem boundedNativePolynomialFamily_baseChange [IsLocallyNoetherian M.left]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (q : ℕ → ℕ) {T U : Over S} (a : U ⟶ T) (x : T ⟶ M)
    (hx : x ∈ (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) :
    PolynomialFamily.GradedHilbert.boundedNativePolynomialFamily M g N hg q (a ≫ x)
        ((Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).map a.op hx) =
      Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (nativePolynomialTestMap M a x)
        (PolynomialFamily.GradedHilbert.boundedNativePolynomialFamily M g N hg q x hx) := by
  apply Subtype.ext
  exact nativePolynomialIdeal_baseChange M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) a x

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialNaturality.GradedHilbert
