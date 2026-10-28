import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeClassifyingMap

/-! # Relative Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The global parameter map of a smooth relative Hilbert family is unique, detected on arbitrary affine tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} {n B N : ℕ} {P : Polynomial ℚ}
variable (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth F.family.scheme.hom]
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothClassifyingMap_unique
    (g : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N)
    (hg : ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ T.left),
      Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (x ≫ g.left) hflat = (F.affineFamily x).val) :
    g = F.smoothClassifyingMap hN hflat := by
  apply Over.OverMorphism.ext
  apply T.left.affineOpenCover.openCover.hom_ext
  intro i
  let R := T.left.affineOpenCover.X i
  let x := T.left.affineOpenCover.f i
  have : Smooth (F.affineFamily x).val.scheme.hom := F.affineFamily_smooth x
  let a : Over.mk (x ≫ T.hom) ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N :=
    Over.homMk (x ≫ g.left) (by
      rw [Category.assoc, g.w]
      rfl)
  have he : a = F.smoothAffinePoint hN hflat x := SmoothHilbert.AffineUniqueness.smoothHilbertAffinePoint_unique
    (F.affineFamily x) hN hflat (x ≫ T.hom) a (F.smoothAffinePoint hN hflat x)
    (hg R x) (F.smoothAffinePoint_pullback hN hflat x)
  exact (congrArg Over.Hom.left he).trans (F.smoothClassifyingMap_affine hN hflat x).symm

include hN in
theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.existsUnique_smoothClassifyingMap :
    ∃! g : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N,
      ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ T.left),
        Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (x ≫ g.left) hflat = (F.affineFamily x).val :=
  ⟨F.smoothClassifyingMap hN hflat, fun _ x => F.smoothClassifyingMap_pullback hN hflat x,
    F.smoothClassifyingMap_unique hN hflat⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
