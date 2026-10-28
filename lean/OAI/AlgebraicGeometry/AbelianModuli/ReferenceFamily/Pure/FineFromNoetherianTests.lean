import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.FineNoetherianTests
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverOpenCoverGluing

/-! # Fine From Noetherian Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure

noncomputable section

/-! For an actual rational quasi-projective candidate, classification
on Noetherian test schemes implies the original all-test fine-moduli
property. Affine classifiers come from the genuine rational Noetherian
models, and their original family comparisons glue by modeled-target
isomorphism descent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence

variable {g N : ℕ} {δ : Fin g → ℕ}

theorem Fine.PurePolarizedModel.isFine_of_noetherian_classification
    (M : Fine.PurePolarizedModel g δ N (Spec (.of ℚ)))
    (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space)
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hM : ∀ (V : Over (Spec (.of ℚ))), IsNoetherian V.left →
      ∀ (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N V.left),
        ∃! c : V ⟶ M.space, Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) B)) :
    M.IsFine := by
  classical
  intro T A
  let C := T.left.affineOpenCover.openCover
  let U (i : C.I₀) : Over (Spec (.of ℚ)) := Over.mk (C.f i ≫ T.hom)
  have hpoints (i : C.I₀) :
      ∃ c : U i ⟶ M.space,
        Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) (A.pullback (C.f i))) := by
    let : IsAffine (U i).left := inferInstanceAs (IsAffine (Spec (T.left.affineOpenCover.X i)))
    exact (M.classifies_affine_of_noetherian_classification Q hg hδ hN hM (U i) (A.pullback (C.f i))).exists
  choose localPoint hlocalPoint using hpoints
  let localIso (i : C.I₀) := (hlocalPoint i).some
  have compatible (i j : C.I₀) :
      pullback.fst (C.f i) (C.f j) ≫ (localPoint i).left =
        pullback.snd (C.f i) (C.f j) ≫ (localPoint j).left := by
    let p := pullback.fst (C.f i) (C.f j)
    let q := pullback.snd (C.f i) (C.f j)
    let V : Over (Spec (.of ℚ)) := Over.mk (p ≫ C.f i ≫ T.hom)
    let a : V ⟶ U i := Over.homMk p rfl
    have hw : q ≫ (C.f j ≫ T.hom) = p ≫ (C.f i ≫ T.hom) :=
      (Category.assoc q (C.f j) T.hom).symm.trans
        ((congrArg (fun r => r ≫ T.hom)
          (pullback.condition (f := C.f i) (g := C.f j)).symm).trans
          (Category.assoc p (C.f i) T.hom))
    let b : V ⟶ U j := Over.homMk q hw
    let ea : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback (a ≫ localPoint i).left)
        ((A.pullback (C.f i)).pullback p) :=
      (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal (localPoint i).left p).symm.trans
        ((localIso i).pullback p)
    let eb : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback (b ≫ localPoint j).left)
        ((A.pullback (C.f j)).pullback q) :=
      (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal (localPoint j).left q).symm.trans
        ((localIso j).pullback q)
    let eab := HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.baseSquare A (C.f i) (C.f j) p q
      (pullback.condition (f := C.f i) (g := C.f j))
    exact congrArg Over.Hom.left
      (M.points_eq_of_noetherian_classification Q hδ hN hM
        (a ≫ localPoint i) (b ≫ localPoint j) ⟨(ea.trans eab).trans eb.symm⟩)
  let c : T ⟶ M.space := OverOpenCoverGluing.glueOverOpenCover T M.space C (fun i => (localPoint i).left)
    (fun i => (localPoint i).w) compatible
  have hc (i : C.I₀) : C.f i ≫ c.left = (localPoint i).left :=
    OverOpenCoverGluing.glueOverOpenCover_fac T M.space C (fun i => (localPoint i).left)
      (fun i => (localPoint i).w) compatible i
  let : IsNoetherian M.space.left := Q.noetherian
  have hfamily (i : C.I₀) : Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback (C.f i))
      ((M.universal.pullback c.left).pullback (C.f i))) := by
    let ec := HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps M.universal (localPoint i).left
      (C.f i ≫ c.left) (hc i).symm
    exact ⟨((localIso i).symm.trans ec).trans
      (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal c.left (C.f i)).symm⟩
  obtain ⟨e⟩ := HilbertConstruction.ModeledTargetIsoExistence.levelIso_nonempty_of_openCover_modeledTarget M.universal c.left A hN C hfamily
  refine ⟨c, ⟨e.symm⟩, ?_⟩
  intro b hb
  obtain ⟨eb⟩ := hb
  exact M.points_eq_of_noetherian_classification Q hδ hN hM b c ⟨eb.trans e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure
