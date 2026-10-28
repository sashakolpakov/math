import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.BaseChangeFunctionSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Normalized Line Open Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! Normalized lines on every test of a locally Noetherian abelian
family are determined by their relative Picard class. In particular,
actual normalized line isomorphisms descend from arbitrary open covers. -/

universe v
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : Schemes.AbelianScheme g S)

theorem Schemes.AbelianScheme.iteratedBaseChangeSection_globalFunctions_bijective
    {T Y : Scheme.{0}} {a : Y ⟶ A.scheme.left} {q : Y ⟶ T} {t : T ⟶ S}
    (H : IsPullback a q A.scheme.hom t)
    (y : T ⟶ Y) (hy : y ≫ q = 𝟙 _) (U : Over T) :
    Function.Bijective ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app U).left.appTop := by
  have H' : IsPullback (pullback.snd U.hom q ≫ a) (pullback.fst U.hom q)
      A.scheme.hom (U.hom ≫ t) := (IsPullback.of_hasPullback U.hom q).flip.paste_horiz H
  let : IsIso (pullback.fst U.hom q).appTop :=
    ReferenceFamily.Abelian.BaseChangeFunctionSheaf.abelian_baseChange_globalFunctions_isIso A _ _ _ H'
  let : IsIso ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app U).left.appTop :=
    Proper.FieldBaseChangeConstants.section_globalFunctions_isIso (pullback.fst U.hom q)
      ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app U).left (Section.BaseChangeFunctor.familyBaseChangeSection_fst q y hy U)
  exact ConcreteCategory.bijective_of_isIso _

theorem Schemes.AbelianScheme.bundleIso_of_relativePicard_eq (T : Over S)
    (L M : Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (zL : (L.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).sheaf ≅ Line.Bundles.structureModule T.left)
    (zM : (M.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).sheaf ≅ Line.Bundles.structureModule T.left)
    (h : (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf L) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) :=
  Picard.ClassIsoDescent.bundleIso_of_relativePicard_eq A.scheme T L M (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A T) (zL ≪≫ zM.symm)
    (A.iteratedBaseChangeSection_globalFunctions_bijective
      (IsPullback.of_hasPullback T.hom A.scheme.hom).flip
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A T)) h

/-- Each cover member carries the usual product with the fixed family.
Only the actual zero frames are needed to remove possible base twists. -/
theorem Schemes.AbelianScheme.normalizedLineIso_of_openCover (T : Over S)
    (L M : Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (zL : (L.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).sheaf ≅ Line.Bundles.structureModule T.left)
    (zM : (M.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).sheaf ≅ Line.Bundles.structureModule T.left)
    (C : T.left.OpenCover.{v})
    (h : ∀ i,
      let V : Over S := Over.mk (C.f i ≫ T.hom)
      let j : V ⟶ T := Over.homMk (C.f i) rfl
      Line.Bundles.LineBundle.pullbackClass (j ▷ A.scheme).left (Line.Bundles.LineBundle.classOf L) =
        Line.Bundles.LineBundle.pullbackClass (j ▷ A.scheme).left (Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let V : C.I₀ → Over S := fun i => Over.mk (C.f i ≫ T.hom)
  let j : ∀ i, V i ⟶ T := fun i => Over.homMk (C.f i) rfl
  let R := Sieve.ofArrows V j
  have hR : R ∈ (Scheme.fppfTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
      _ C.mem_grothendieckTopology
  apply A.bundleIso_of_relativePicard_eq T L M zL zM
  apply Picard.LocalEquality.relativePicard_eq_of_local_bundle_iso A.scheme T L M R hR
  intro U f hf
  obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff V j f).mp hf
  have hi : (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (j i).op (Line.Bundles.LineBundle.classOf L) =
      (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (j i).op (Line.Bundles.LineBundle.classOf M) := h i
  have he : (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op (Line.Bundles.LineBundle.classOf L) =
      (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op (Line.Bundles.LineBundle.classOf M) := by
    rw [ha]
    exact ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_comp_apply (j i).op a.op _).trans
      ((congrArg ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map a.op) hi).trans
        ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_comp_apply (j i).op a.op _).symm)
  exact Quotient.exact (s := Line.Bundles.LineBundle.isoSetoid _)
    (a := L.pullback ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map f))
    (b := M.pullback ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map f)) he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
