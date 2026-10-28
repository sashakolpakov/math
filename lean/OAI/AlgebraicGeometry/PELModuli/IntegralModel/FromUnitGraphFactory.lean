import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.FineNoetherianTests
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DegreePolarizedNoetherianModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverOpenCoverGluing

/-! # From Unit Graph Factory -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-! Unit-degree graph parameters reduce the original all-test fine
moduli property to classification on Noetherian schemes over the same base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence

variable {R : Type} [CommRing R] [IsNoetherianRing R]
    {g N : ℕ} {δ : Fin g → ℕ}

theorem AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel.classifies_spec_of_unitGraphFactory
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel g δ N (Spec (.of R)))
    (Q : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space)
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNR : IsUnit (N : R))
    (Φ : ∀ d : ℕ, 0 < d → IsUnit (d : R) → AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)
    (hM : ∀ (V : Over (Spec (.of R))), IsNoetherian V.left →
      ∀ (B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N V.left),
        ∃! c : V ⟶ M.space, Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) B))
    (C : CommRingCat) (q : Spec C ⟶ Spec (.of R))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C)) :
    ∃! c : Over.mk q ⟶ M.space,
      Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) A) := by
  obtain ⟨V, hV, B, t, ⟨e⟩⟩ := A.exists_noetherianModel_over_spec C q hg hδ hN hNR Φ
  obtain ⟨b, ⟨eb⟩, _⟩ := hM V hV B
  let c : Over.mk q ⟶ M.space := t ≫ b
  let ec : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) A :=
    (((AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal b.left t.left).symm.trans
      (eb.pullback t.left)).trans e.symm)
  refine ⟨c, ⟨ec⟩, ?_⟩
  intro k hk
  obtain ⟨ek⟩ := hk
  exact M.points_eq_of_noetherian_classification Q hδ hN hM k c ⟨ek.trans ec.symm⟩

theorem AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel.isFine_of_unitGraphFactory
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel g δ N (Spec (.of R)))
    (Q : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space)
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNR : IsUnit (N : R))
    (Φ : ∀ d : ℕ, 0 < d → IsUnit (d : R) → AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)
    (hM : ∀ (V : Over (Spec (.of R))), IsNoetherian V.left →
      ∀ (B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N V.left),
        ∃! c : V ⟶ M.space, Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) B)) :
    M.IsFine := by
  classical
  intro T A
  let C := T.left.affineOpenCover.openCover
  let U (i : C.I₀) : Over (Spec (.of R)) := Over.mk (C.f i ≫ T.hom)
  have hpoints (i : C.I₀) :
      ∃ c : U i ⟶ M.space,
        Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) (A.pullback (C.f i))) := by
    exact (M.classifies_spec_of_unitGraphFactory Q hg hδ hN hNR Φ hM
      (T.left.affineOpenCover.X i) (C.f i ≫ T.hom) (A.pullback (C.f i))).exists
  choose localPoint hlocalPoint using hpoints
  let localIso (i : C.I₀) := (hlocalPoint i).some
  have compatible (i j : C.I₀) :
      pullback.fst (C.f i) (C.f j) ≫ (localPoint i).left =
        pullback.snd (C.f i) (C.f j) ≫ (localPoint j).left := by
    let p := pullback.fst (C.f i) (C.f j)
    let q := pullback.snd (C.f i) (C.f j)
    let V : Over (Spec (.of R)) := Over.mk (p ≫ C.f i ≫ T.hom)
    let a : V ⟶ U i := Over.homMk p rfl
    have hw : q ≫ (C.f j ≫ T.hom) = p ≫ (C.f i ≫ T.hom) :=
      (Category.assoc q (C.f j) T.hom).symm.trans
        ((congrArg (fun r => r ≫ T.hom)
          (pullback.condition (f := C.f i) (g := C.f j)).symm).trans
          (Category.assoc p (C.f i) T.hom))
    let b : V ⟶ U j := Over.homMk q hw
    let ea : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback (a ≫ localPoint i).left)
        ((A.pullback (C.f i)).pullback p) :=
      (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal (localPoint i).left p).symm.trans
        ((localIso i).pullback p)
    let eb : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback (b ≫ localPoint j).left)
        ((A.pullback (C.f j)).pullback q) :=
      (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal (localPoint j).left q).symm.trans
        ((localIso j).pullback q)
    let eab := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.baseSquare A (C.f i) (C.f j) p q
      (pullback.condition (f := C.f i) (g := C.f j))
    exact congrArg Over.Hom.left
      (M.points_eq_of_noetherian_classification Q hδ hN hM
        (a ≫ localPoint i) (b ≫ localPoint j) ⟨(ea.trans eab).trans eb.symm⟩)
  let c : T ⟶ M.space := AbelianModuli.ReferenceFamily.OverOpenCoverGluing.glueOverOpenCover T M.space C (fun i => (localPoint i).left)
    (fun i => (localPoint i).w) compatible
  have hc (i : C.I₀) : C.f i ≫ c.left = (localPoint i).left :=
    AbelianModuli.ReferenceFamily.OverOpenCoverGluing.glueOverOpenCover_fac T M.space C (fun i => (localPoint i).left)
      (fun i => (localPoint i).w) compatible i
  let : IsNoetherian M.space.left := Q.noetherian
  have hfamily (i : C.I₀) : Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback (C.f i))
      ((M.universal.pullback c.left).pullback (C.f i))) := by
    let ec := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps M.universal (localPoint i).left
      (C.f i ≫ c.left) (hc i).symm
    exact ⟨((localIso i).symm.trans ec).trans
      (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal c.left (C.f i)).symm⟩
  obtain ⟨e⟩ := AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence.levelIso_nonempty_of_openCover_modeledTarget M.universal c.left A hN C hfamily
  refine ⟨c, ⟨e.symm⟩, ?_⟩
  intro b hb
  obtain ⟨eb⟩ := hb
  exact M.points_eq_of_noetherian_classification Q hδ hN hM b c ⟨eb.trans e⟩

end

end OAI.AlgebraicGeometry
