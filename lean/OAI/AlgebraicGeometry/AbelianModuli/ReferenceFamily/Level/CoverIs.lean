import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel

/-! # Cover Is -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.CoverIs.LevelCover

noncomputable section

/-! The finite etale parameter scheme is a covering on any connected
base where a single actual projective complex fiber exists. The clopen
image argument propagates existence across the entire connected base;
no global level or geometric-fiber marking is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K)) [NeZero N]

theorem fullFrame_image_isClopen :
    IsClopen (Set.range (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom) := by
  obtain ⟨hf, he⟩ := Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p (N := N)
  let : IsFinite (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := hf
  let : Etale (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := he
  exact ⟨(Frame.Locus.LevelCover.fullFrameScheme A p).hom.isClosedMap.isClosed_range,
    (Frame.Locus.LevelCover.fullFrameScheme A p).hom.isOpenMap.isOpen_range⟩

/-- On a connected base the finite etale full-level parameter scheme
is a covering as soon as it has one point. -/
theorem fullFrame_surjective_of_nonempty [PreconnectedSpace S]
    [Nonempty (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).left] :
    Surjective (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := by
  have hr : (Set.range (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom).Nonempty :=
    Set.range_nonempty _
  have hall := (fullFrame_image_isClopen A p (N := N)).eq_univ hr
  constructor
  intro s
  have hs : s ∈ Set.range (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := by
    rw [hall]
    trivial
  exact hs

/-- An actual complex projective fiber supplies a point of the
full-level parameter scheme, via its proved native torsion group. -/
theorem fullFrame_nonempty_of_complex_fiber (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.pullback q).scheme.left (A.pullback q).scheme.hom) :
    Nonempty (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).left := by
  let β := Complex.ComplexLevel.fullLevel (A.pullback q) P N
  let f := Frame.Factorization.LevelCover.fullFrameOfRelativeLevel A p (Over.mk q) β
  exact ⟨f.left (default : Foundations.Scheme.ProjectiveSpace.complexBase)⟩

/-- Native complex torsion and the clopen image produce a surjective
finite etale cover with a universal full level on the original family. -/
theorem fullFrame_surjective_of_complex_fiber [PreconnectedSpace S]
    (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.pullback q).scheme.left (A.pullback q).scheme.hom) :
    Surjective (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := by
  let : Nonempty (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).left :=
    fullFrame_nonempty_of_complex_fiber A p q P
  exact fullFrame_surjective_of_nonempty A p

include p in
/-- A concrete finite etale surjective covering on which the original
abelian scheme has a constructed full level. -/
theorem exists_fullLevel_cover_of_complex_fiber [PreconnectedSpace S]
    (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.pullback q).scheme.left (A.pullback q).scheme.hom) :
    ∃ (S' : Scheme.{0}) (u : S' ⟶ S),
      IsFinite u ∧ Etale u ∧ Surjective u ∧ Nonempty ((A.pullback u).FullLevel N) :=
  ⟨(Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).left, (Frame.Locus.LevelCover.fullFrameScheme A p).hom,
    (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).1, (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).2,
    fullFrame_surjective_of_complex_fiber A p q P, ⟨Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A p⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.CoverIs.LevelCover
