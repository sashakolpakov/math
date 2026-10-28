import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverOpenCoverGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseSquareIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence

/-! # Noetherian Cover Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure

noncomputable section

/-! Local classifiers on an open cover of a locally Noetherian test
scheme glue to a unique classifier for an actual quasi-projective pure
model. The point-separation input is used on the actual scheme overlaps;
the comparison of the original families descends to the modeled target. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- Internal passage from open-cover classification to classification on
a locally Noetherian test scheme. The separation hypothesis concerns the
original full-level polarized families. -/
theorem Fine.PurePolarizedModel.classifies_of_locallyNoetherian_openCover
    {S : Scheme.{0}} [IsNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ}
    (M : Fine.PurePolarizedModel g δ N S)
    (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space) (hN : 3 ≤ N)
    (hsep : ∀ (V : Over S) [IsLocallyNoetherian V.left]
      (a b : V ⟶ M.space),
      HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback a.left)
        (M.universal.pullback b.left) → a = b)
    {T : Over S} [IsLocallyNoetherian T.left]
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (C : T.left.OpenCover)
    (localPoint : ∀ i : C.I₀, Over.mk (C.f i ≫ T.hom) ⟶ M.space)
    (localIso : ∀ i : C.I₀,
      HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback (localPoint i).left)
        (A.pullback (C.f i))) :
    ∃! c : T ⟶ M.space,
      Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) A) := by
  classical
  let U (i : C.I₀) : Over S := Over.mk (C.f i ≫ T.hom)
  have compatible (i j : C.I₀) :
      pullback.fst (C.f i) (C.f j) ≫ (localPoint i).left =
        pullback.snd (C.f i) (C.f j) ≫ (localPoint j).left := by
    let p := pullback.fst (C.f i) (C.f j)
    let q := pullback.snd (C.f i) (C.f j)
    let V : Over S := Over.mk (p ≫ C.f i ≫ T.hom)
    let : IsLocallyNoetherian (C.X i) :=
      isLocallyNoetherian_of_isOpenImmersion (C.f i)
    let : IsLocallyNoetherian V.left :=
      isLocallyNoetherian_of_isOpenImmersion p
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
      (hsep V (a ≫ localPoint i) (b ≫ localPoint j) ((ea.trans eab).trans eb.symm))
  let c : T ⟶ M.space :=
    OverOpenCoverGluing.glueOverOpenCover T M.space C (fun i => (localPoint i).left)
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
  obtain ⟨e⟩ :=
    HilbertConstruction.ModeledTargetIsoExistence.levelIso_nonempty_of_openCover_modeledTarget M.universal c.left A hN C hfamily
  refine ⟨c, ⟨e.symm⟩, ?_⟩
  intro b hb
  obtain ⟨eb⟩ := hb
  exact hsep T b c (eb.trans e)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure
