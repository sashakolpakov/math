import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.BoundedPolynomialFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialPointComparison

/-! # Polynomial Inclusion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialInclusion

noncomputable section

/-! The transported polynomial Hilbert family is the kernel of an actual
closed immersion into the projective ambient over the original base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem closedImmersion_comp_iso_ker {A B C : Scheme.{u}} (f : A ⟶ B)
    [IsClosedImmersion f] (e : B ≅ C) : (f ≫ e.hom).ker = f.ker.comap e.inv := by
  have H : IsPullback (f ≫ e.hom) (𝟙 A) e.inv f :=
    IsPullback.of_vert_isIso ⟨by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]⟩
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

namespace GradedHilbert

variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) {T : Over S} (x : T ⟶ M)

def globalPolynomialInclusion : Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily M I x ⟶
    Hilbert.Functor.ambient (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T :=
  Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x ≫ (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M x).hom

instance globalPolynomialInclusion_isClosedImmersion : IsClosedImmersion (globalPolynomialInclusion M I x) :=
  inferInstanceAs (IsClosedImmersion (Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x ≫ (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M x).hom))

theorem globalPolynomialInclusion_projection :
    globalPolynomialInclusion M I x ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T =
      Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x := by
  rw [globalPolynomialInclusion, Category.assoc, ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso_projection,
    Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection]

theorem globalPolynomialInclusion_projective :
    globalPolynomialInclusion M I x ≫
        (prod.snd : T ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
      Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x ≫
        (prod.snd : Over.mk x.left ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left ≫
          Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap M.hom n := by
  rw [globalPolynomialInclusion, Category.assoc, ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso_projective]

theorem globalPolynomialInclusion_ker :
    (globalPolynomialInclusion M I x).ker =
      (Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x).ker.comap (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M x).inv :=
  closedImmersion_comp_iso_ker _ _

theorem globalBoundedPolynomialFamily_val [IsLocallyNoetherian M.left]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (q : ℕ → ℕ) (hx : x ∈ (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) :
    (BoundedPolynomialFamily.GradedHilbert.globalBoundedPolynomialFamily M g N hg q x hx).val =
      (globalPolynomialInclusion M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) x).ker :=
  (globalPolynomialInclusion_ker M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) x).symm

end GradedHilbert

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialInclusion
