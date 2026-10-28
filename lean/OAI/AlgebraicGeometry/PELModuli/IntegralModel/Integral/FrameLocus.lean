import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.GroupScheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Finiteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionDivision
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Frame Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameLocus.IntegralLevelCover

noncomputable section

/-! Adapted from FrameFullLocus to an arbitrary base on which N is a unit.
The full-frame locus is an actual clopen subscheme. It removes base
points over which the universal frame omits a torsion point. Its
construction uses the proved monomorphism and finite etaleness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g N : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem frameSchemeMap_finite [NeZero N] (T : Over S) (f : T ⟶ AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) :
    IsFinite (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left := by
  have hc : IsFinite (AbelianModuli.HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left).hom :=
    AbelianModuli.HilbertConstruction.Finite.ConstantScheme.constantScheme_finite (S := T.left) (I := ULift (Multiplicative (Fin (2 * g) → ZMod N)))
  have hm : IsFinite ((AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left ≫ ((A.pullback T.hom).torsionScheme N).hom) := by
    rw [(AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).w]
    exact hc
  let : IsFinite ((AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left ≫ ((A.pullback T.hom).torsionScheme N).hom) := hm
  exact IsFinite.of_comp (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left ((A.pullback T.hom).torsionScheme N).hom

theorem frameSchemeMap_closed [NeZero N] (T : Over S) (f : T ⟶ AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) :
    IsClosedImmersion (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left := by
  let : Mono (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f) := AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap_mono A T f
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨frameSchemeMap_finite A T f, inferInstance⟩

theorem frameSchemeMap_etale (T : Over S) (f : T ⟶ AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N)
    [Etale ((A.pullback T.hom).torsionScheme N).hom] :
    Etale (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left := by
  have hc : Etale (AbelianModuli.HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left).hom := AbelianModuli.HilbertConstruction.Level.Scheme.constantScheme_etale T.left _
  have hm : Etale ((AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left ≫ ((A.pullback T.hom).torsionScheme N).hom) := by
    rw [(AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).w]
    exact hc
  let : Etale ((AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left ≫ ((A.pullback T.hom).torsionScheme N).hom) := hm
  exact Etale.of_comp (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left ((A.pullback T.hom).torsionScheme N).hom

theorem frameSchemeMap_open [NeZero N] (T : Over S) (f : T ⟶ AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N)
    [Etale ((A.pullback T.hom).torsionScheme N).hom] :
    IsOpenImmersion (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left := by
  let : Mono (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f) := AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap_mono A T f
  let : Etale (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A T f).left := frameSchemeMap_etale A T f
  exact IsOpenImmersion.of_flat_of_mono _

def frameMissingOpen [NeZero N] :
    ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).left.Opens :=
  ⟨(Set.range (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left)ᶜ,
    by
      let : IsClosedImmersion (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left :=
        frameSchemeMap_closed A _ _
      exact (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

def frameMissingProjection [NeZero N] :
    (frameMissingOpen A (N := N)).toScheme ⟶ (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).left :=
  (frameMissingOpen A (N := N)).ι ≫ ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom

variable (hN : ∀ x : S, IsUnit (N : S.presheaf.stalk x))

include hN in
theorem frameMissingProjection_finite_etale [NeZero N] :
    IsFinite (frameMissingProjection (N := N) A) ∧ Etale (frameMissingProjection (N := N) A) := by
  obtain ⟨hf, he⟩ := TorsionDivision.torsionScheme_finite_etale
    (A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom) N (fun x => by
      simpa only [map_natCast] using (hN ((AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom x)).map
        ((AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom.stalkMap x).hom)
  let : IsFinite ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom := hf
  let : Etale ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom := he
  let : IsOpenImmersion (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left :=
    frameSchemeMap_open A _ _
  have hclosed : IsClosed (frameMissingOpen (N := N) A :
      Set ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).left) :=
    (IsOpenImmersion.isOpen_range (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left).isClosed_compl
  have hi : IsClosedImmersion (frameMissingOpen (N := N) A).ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact hclosed
  let : IsClosedImmersion (frameMissingOpen (N := N) A).ι := hi
  exact ⟨inferInstanceAs (IsFinite ((frameMissingOpen A).ι ≫ _)),
    inferInstanceAs (Etale ((frameMissingOpen A).ι ≫ _))⟩

def fullFrameOpen [NeZero N] : (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).left.Opens :=
  ⟨(Set.range (frameMissingProjection (N := N) A))ᶜ, by
    have hf := (frameMissingProjection_finite_etale A hN (N := N)).1
    let : IsFinite (frameMissingProjection (N := N) A) := hf
    exact (frameMissingProjection (N := N) A).isClosedMap.isClosed_range.isOpen_compl⟩

theorem fullFrameOpen_isClosed [NeZero N] :
    IsClosed (fullFrameOpen A hN (N := N) : Set (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).left) := by
  have he := (frameMissingProjection_finite_etale A hN (N := N)).2
  let : Etale (frameMissingProjection (N := N) A) := he
  exact (frameMissingProjection (N := N) A).isOpenMap.isOpen_range.isClosed_compl

theorem mem_fullFrameOpen_iff [NeZero N] (s : (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).left) :
    s ∈ fullFrameOpen A hN (N := N) ↔
      ∀ y : ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).left,
        ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom y = s →
          y ∈ Set.range (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left := by
  constructor
  · intro hs y hy
    by_contra hmissing
    exact hs ⟨⟨y, hmissing⟩, hy⟩
  · intro hs hmissing
    obtain ⟨y, hy⟩ := hmissing
    exact y.property (hs y.val hy)

def fullFrameTorsionOpen [NeZero N] :
    ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).left.Opens :=
  ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom ⁻¹ᵁ fullFrameOpen A hN

/-- On the spanning locus, the actual pullback of the universal
coefficient morphism is an isomorphism of schemes. -/
theorem universalFrame_pullback_isIso [NeZero N] :
    IsIso (Limits.pullback.snd
      (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left (fullFrameTorsionOpen A hN).ι) := by
  have he := (TorsionDivision.torsionScheme_finite_etale (A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom) N (fun x => by
      simpa only [map_natCast] using (hN ((AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom x)).map
        ((AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom.stalkMap x).hom)).2
  let : Etale ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom := he
  let : IsOpenImmersion (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left :=
    frameSchemeMap_open A _ _
  have hs : Surjective (Limits.pullback.snd
      (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left (fullFrameTorsionOpen A hN).ι) := by
    constructor
    intro y
    have hy : y ∈ Set.range (Limits.pullback.snd
        (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left (fullFrameTorsionOpen A hN).ι) := by
      rw [Scheme.Pullback.range_snd]
      exact (mem_fullFrameOpen_iff A hN _).mp y.property y.val rfl
    exact hy
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hs⟩

def fullFrameScheme [NeZero N] : Over S :=
  Over.mk ((fullFrameOpen A hN (N := N)).ι ≫ (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom)

theorem fullFrameScheme_finite_etale [NeZero N] :
    IsFinite (fullFrameScheme A hN (N := N)).hom ∧ Etale (fullFrameScheme A hN (N := N)).hom := by
  obtain ⟨htf, hte⟩ := TorsionDivision.torsionScheme_finite_etale A N hN
  let : IsFinite (A.torsionScheme N).hom := htf
  let : Etale (A.torsionScheme N).hom := hte
  obtain ⟨hf, he⟩ := AbelianModuli.ReferenceFamily.Frame.Finiteness.LevelCover.frameScheme_finite_etale A (N := N)
  let : IsFinite (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom := hf
  let : Etale (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom := he
  have hi : IsClosedImmersion (fullFrameOpen A hN (N := N)).ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact fullFrameOpen_isClosed A hN
  let : IsClosedImmersion (fullFrameOpen A hN (N := N)).ι := hi
  exact ⟨inferInstanceAs (IsFinite ((fullFrameOpen A hN).ι ≫ _)),
    inferInstanceAs (Etale ((fullFrameOpen A hN).ι ≫ _))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameLocus.IntegralLevelCover
