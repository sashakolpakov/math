import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.GroupScheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Locus.LevelCover

noncomputable section

/-! The full-frame locus is an actual clopen subscheme. It removes base
points over which the universal frame omits a torsion point. Its
construction uses the proved monomorphism and finite etaleness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem frameSchemeMap_finite [NeZero N] (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    IsFinite (GroupScheme.LevelCover.frameSchemeMap A T f).left := by
  have hc : IsFinite (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left).hom :=
    HilbertConstruction.Finite.ConstantScheme.constantScheme_finite (S := T.left) (I := ULift (Multiplicative (Fin (2 * g) → ZMod N)))
  have hm : IsFinite ((GroupScheme.LevelCover.frameSchemeMap A T f).left ≫ ((A.pullback T.hom).torsionScheme N).hom) := by
    rw [(GroupScheme.LevelCover.frameSchemeMap A T f).w]
    exact hc
  let : IsFinite ((GroupScheme.LevelCover.frameSchemeMap A T f).left ≫ ((A.pullback T.hom).torsionScheme N).hom) := hm
  exact IsFinite.of_comp (GroupScheme.LevelCover.frameSchemeMap A T f).left ((A.pullback T.hom).torsionScheme N).hom

theorem frameSchemeMap_closed [NeZero N] (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    IsClosedImmersion (GroupScheme.LevelCover.frameSchemeMap A T f).left := by
  let : Mono (GroupScheme.LevelCover.frameSchemeMap A T f) := GroupScheme.LevelCover.frameSchemeMap_mono A T f
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨frameSchemeMap_finite A T f, inferInstance⟩

theorem frameSchemeMap_etale (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    [Etale ((A.pullback T.hom).torsionScheme N).hom] :
    Etale (GroupScheme.LevelCover.frameSchemeMap A T f).left := by
  have hc : Etale (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left).hom := HilbertConstruction.Level.Scheme.constantScheme_etale T.left _
  have hm : Etale ((GroupScheme.LevelCover.frameSchemeMap A T f).left ≫ ((A.pullback T.hom).torsionScheme N).hom) := by
    rw [(GroupScheme.LevelCover.frameSchemeMap A T f).w]
    exact hc
  let : Etale ((GroupScheme.LevelCover.frameSchemeMap A T f).left ≫ ((A.pullback T.hom).torsionScheme N).hom) := hm
  exact Etale.of_comp (GroupScheme.LevelCover.frameSchemeMap A T f).left ((A.pullback T.hom).torsionScheme N).hom

theorem frameSchemeMap_open [NeZero N] (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    [Etale ((A.pullback T.hom).torsionScheme N).hom] :
    IsOpenImmersion (GroupScheme.LevelCover.frameSchemeMap A T f).left := by
  let : Mono (GroupScheme.LevelCover.frameSchemeMap A T f) := GroupScheme.LevelCover.frameSchemeMap_mono A T f
  let : Etale (GroupScheme.LevelCover.frameSchemeMap A T f).left := frameSchemeMap_etale A T f
  exact IsOpenImmersion.of_flat_of_mono _

def frameMissingOpen [NeZero N] :
    ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).left.Opens :=
  ⟨(Set.range (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left)ᶜ,
    by
      let : IsClosedImmersion (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left :=
        frameSchemeMap_closed A _ _
      exact (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

def frameMissingProjection [NeZero N] :
    (frameMissingOpen A (N := N)).toScheme ⟶ (Level.Cover.LevelCover.frameScheme A N).left :=
  (frameMissingOpen A (N := N)).ι ≫ ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom

variable {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))

include p in
theorem frameMissingProjection_finite_etale [NeZero N] :
    IsFinite (frameMissingProjection (N := N) A) ∧ Etale (frameMissingProjection (N := N) A) := by
  obtain ⟨hf, he⟩ := TorsionEtaleAt.TorsionEtale.torsion_finite_etale
    (A.pullback (Level.Cover.LevelCover.frameScheme A N).hom) ((Level.Cover.LevelCover.frameScheme A N).hom ≫ p) N
  let : IsFinite ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom := hf
  let : Etale ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom := he
  let : IsOpenImmersion (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left :=
    frameSchemeMap_open A _ _
  have hclosed : IsClosed (frameMissingOpen (N := N) A :
      Set ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).left) :=
    (IsOpenImmersion.isOpen_range (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left).isClosed_compl
  have hi : IsClosedImmersion (frameMissingOpen (N := N) A).ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact hclosed
  let : IsClosedImmersion (frameMissingOpen (N := N) A).ι := hi
  exact ⟨inferInstanceAs (IsFinite ((frameMissingOpen A).ι ≫ _)),
    inferInstanceAs (Etale ((frameMissingOpen A).ι ≫ _))⟩

def fullFrameOpen [NeZero N] : (Level.Cover.LevelCover.frameScheme A N).left.Opens :=
  ⟨(Set.range (frameMissingProjection (N := N) A))ᶜ, by
    have hf := (frameMissingProjection_finite_etale A p (N := N)).1
    let : IsFinite (frameMissingProjection (N := N) A) := hf
    exact (frameMissingProjection (N := N) A).isClosedMap.isClosed_range.isOpen_compl⟩

theorem fullFrameOpen_isClosed [NeZero N] :
    IsClosed (fullFrameOpen A p (N := N) : Set (Level.Cover.LevelCover.frameScheme A N).left) := by
  have he := (frameMissingProjection_finite_etale A p (N := N)).2
  let : Etale (frameMissingProjection (N := N) A) := he
  exact (frameMissingProjection (N := N) A).isOpenMap.isOpen_range.isClosed_compl

theorem mem_fullFrameOpen_iff [NeZero N] (s : (Level.Cover.LevelCover.frameScheme A N).left) :
    s ∈ fullFrameOpen A p (N := N) ↔
      ∀ y : ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).left,
        ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom y = s →
          y ∈ Set.range (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left := by
  constructor
  · intro hs y hy
    by_contra hmissing
    exact hs ⟨⟨y, hmissing⟩, hy⟩
  · intro hs hmissing
    obtain ⟨y, hy⟩ := hmissing
    exact y.property (hs y.val hy)

def fullFrameTorsionOpen [NeZero N] :
    ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).left.Opens :=
  ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom ⁻¹ᵁ fullFrameOpen A p

/-- On the spanning locus, the actual pullback of the universal
coefficient morphism is an isomorphism of schemes. -/
theorem universalFrame_pullback_isIso [NeZero N] :
    IsIso (Limits.pullback.snd
      (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left (fullFrameTorsionOpen A p).ι) := by
  have he := (TorsionEtaleAt.TorsionEtale.torsion_finite_etale (A.pullback (Level.Cover.LevelCover.frameScheme A N).hom)
    ((Level.Cover.LevelCover.frameScheme A N).hom ≫ p) N).2
  let : Etale ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom := he
  let : IsOpenImmersion (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left :=
    frameSchemeMap_open A _ _
  have hs : Surjective (Limits.pullback.snd
      (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left (fullFrameTorsionOpen A p).ι) := by
    constructor
    intro y
    have hy : y ∈ Set.range (Limits.pullback.snd
        (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left (fullFrameTorsionOpen A p).ι) := by
      rw [Scheme.Pullback.range_snd]
      exact (mem_fullFrameOpen_iff A p _).mp y.property y.val rfl
    exact hy
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hs⟩

def fullFrameScheme [NeZero N] : Over S :=
  Over.mk ((fullFrameOpen A p (N := N)).ι ≫ (Level.Cover.LevelCover.frameScheme A N).hom)

theorem fullFrameScheme_finite_etale [NeZero N] :
    IsFinite (fullFrameScheme A p (N := N)).hom ∧ Etale (fullFrameScheme A p (N := N)).hom := by
  obtain ⟨hf, he⟩ := TorsionEtaleAt.TorsionEtale.frame_finite_etale A p N
  let : IsFinite (Level.Cover.LevelCover.frameScheme A N).hom := hf
  let : Etale (Level.Cover.LevelCover.frameScheme A N).hom := he
  have hi : IsClosedImmersion (fullFrameOpen A p (N := N)).ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact fullFrameOpen_isClosed A p
  let : IsClosedImmersion (fullFrameOpen A p (N := N)).ι := hi
  exact ⟨inferInstanceAs (IsFinite ((fullFrameOpen A p).ι ≫ _)),
    inferInstanceAs (Etale ((fullFrameOpen A p).ι ≫ _))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Locus.LevelCover
