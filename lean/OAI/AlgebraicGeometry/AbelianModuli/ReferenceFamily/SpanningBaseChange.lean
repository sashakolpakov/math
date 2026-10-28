import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Locus

/-! # Spanning Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SpanningBaseChange.LevelCover

noncomputable section

/-! A monomorphism which covers every target point above a chosen base
locus becomes an isomorphism after restricting to that locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

variable {B B' : Scheme.{0}} {X Y : Over B}

theorem overPullbackMap_isPullback (m : X ⟶ Y) (u : B' ⟶ B) :
    IsPullback (pullback.fst X.hom u) ((Over.pullback u).map m).left
      m.left (pullback.fst Y.hom u) := by
  have outer : IsPullback (pullback.fst X.hom u)
      (((Over.pullback u).map m).left ≫ pullback.snd Y.hom u)
      (m.left ≫ Y.hom) u := by
    have hw : ((Over.pullback u).map m).left ≫ pullback.snd Y.hom u =
        pullback.snd X.hom u := ((Over.pullback u).map m).w
    rw [hw, m.w]
    exact IsPullback.of_hasPullback X.hom u
  exact outer.of_bot (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback Y.hom u)

theorem overPullbackMap_isIso_of_spans (m : X ⟶ Y) (u : B' ⟶ B)
    [IsOpenImmersion m.left]
    (hspan : ∀ y : Y.left, Y.hom y ∈ Set.range u → y ∈ Set.range m.left) :
    IsIso ((Over.pullback u).map m) := by
  let sq := overPullbackMap_isPullback m u
  have ho : IsOpenImmersion ((Over.pullback u).map m).left :=
    MorphismProperty.of_isPullback sq (inferInstanceAs (IsOpenImmersion m.left))
  have hs : Surjective ((Over.pullback u).map m).left := by
    constructor
    intro y
    have hy : y ∈ Set.range (pullback.snd m.left (pullback.fst Y.hom u)) := by
      rw [Scheme.Pullback.range_snd]
      apply hspan
      refine ⟨pullback.snd Y.hom u y, ?_⟩
      exact (congrArg (fun q : pullback Y.hom u ⟶ B => q y) (pullback.condition (f := Y.hom) (g := u))).symm
    obtain ⟨z, hz⟩ := hy
    refine ⟨sq.isoPullback.inv z, ?_⟩
    exact (congrArg (fun q : pullback m.left (pullback.fst Y.hom u) ⟶ pullback Y.hom u => q z) sq.isoPullback_inv_snd).trans hz
  have hi : IsIso ((Over.pullback u).map m).left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨ho, hs⟩
  let : IsIso ((Over.forget B').map ((Over.pullback u).map m)) := hi
  exact isIso_of_reflects_iso ((Over.pullback u).map m) (Over.forget B')

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))

theorem universalFrame_overPullback_isIso [NeZero N] :
    IsIso ((Over.pullback (Frame.Locus.LevelCover.fullFrameOpen A p (N := N)).ι).map
      (Frame.GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _))) := by
  have he := (TorsionEtaleAt.TorsionEtale.torsion_finite_etale (A.pullback (Level.Cover.LevelCover.frameScheme A N).hom)
    ((Level.Cover.LevelCover.frameScheme A N).hom ≫ p) N).2
  let : Etale ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom := he
  let : IsOpenImmersion (Frame.GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left :=
    Frame.Locus.LevelCover.frameSchemeMap_open A _ _
  apply overPullbackMap_isIso_of_spans
  intro y hy
  rw [Scheme.Opens.range_ι] at hy
  exact (Frame.Locus.LevelCover.mem_fullFrameOpen_iff A p _).mp hy y rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SpanningBaseChange.LevelCover
