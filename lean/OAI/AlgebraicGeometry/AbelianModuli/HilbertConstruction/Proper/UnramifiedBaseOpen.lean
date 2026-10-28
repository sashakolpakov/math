import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourcePropertyOpenRecovery
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalGroupFiberUnramified
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedFlatDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection

/-! # Unramified Base Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.UnramifiedBaseOpen

noncomputable section

/-! The unramified fibers of a proper morphism form an actual open base.
The criterion uses the original pullback and holds on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

local instance : IsZariskiLocalAtSource (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
  @HasRingHomProperty.instIsZariskiLocalAtSource _ RingHom.FormallyUnramified inferInstance

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]

def properUnramifiedBaseOpen : S.Opens :=
  SourcePropertyBaseOpen.properSourcePropertyBaseOpen (@FormallyUnramified) f

theorem properUnramifiedBaseOpen_restrict :
    FormallyUnramified (f ∣_ properUnramifiedBaseOpen f) :=
  SourcePropertyBaseOpen.properSourcePropertyBaseOpen_restrict (@FormallyUnramified) f

theorem unramified_pullback_of_range_subset {T : Scheme.{u}} (b : T ⟶ S)
    (hb : Set.range b ⊆ properUnramifiedBaseOpen f) :
    FormallyUnramified (pullback.snd f b) :=
  SourcePropertyOpenRecovery.property_pullback_of_range_subset_properBaseOpen (@FormallyUnramified) f b hb

theorem mem_properUnramifiedBaseOpen_of_residueFiber (s : S)
    (h : FormallyUnramified (pullback.snd f (S.fromSpecResidueField s))) :
    s ∈ properUnramifiedBaseOpen f := by
  let := h
  change s ∉ f '' (SourcePropertyOpenLocus.sourcePropertyOpenLocus (@FormallyUnramified) f : Set X)ᶜ
  rintro ⟨x, hx, hxs⟩
  let k : Spec (S.residueField s) := (⊥ : PrimeSpectrum (S.residueField s))
  have hs : f x = S.fromSpecResidueField s k :=
    hxs.trans (S.fromSpecResidueField_apply s k).symm
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback x k hs
  have : Mono (S.fromSpecResidueField s) := inferInstance
  have hu := Picard.ThetaConstruction.LocalGroupFiberUnramified.Geometric.unramified_stalk_of_mono_fieldFiber
    (K := S.residueField s) f (S.fromSpecResidueField s) z
  rw [hz] at hu
  obtain ⟨V, hxV, hV⟩ := Picard.ThetaConstruction.UnramifiedStalkNeighborhood.Geometric.exists_unramified_of_stalk f x hu
  exact hx (SourcePropertyOpenLocus.le_sourcePropertyOpenLocus (@FormallyUnramified) f V hV hxV)

theorem properUnramifiedBaseOpen_field_point
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S) :
    Set.range b ⊆ properUnramifiedBaseOpen f ↔
      FormallyUnramified (pullback.snd f b) := by
  refine ⟨unramified_pullback_of_range_subset f b, fun hb => ?_⟩
  let s := b (IsLocalRing.closedPoint K)
  let φ : S.residueField s ⟶ .of K := S.descResidueField (Scheme.stalkClosedPointTo b)
  let c := Spec.map φ
  let a := S.fromSpecResidueField s
  have hc : c ≫ a = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S b
  have : FormallyUnramified (pullback.snd f (c ≫ a)) := hc.symm ▸ hb
  have ht : FormallyUnramified (pullback.snd (pullback.snd f a) c) :=
    UnramifiedPullbackRefinements.unramified_iterated_pullback f a c
  have hflat : Flat c := Smooth.FieldExtensionReflection.fieldSpecMap_flat φ
  have hsurj : Surjective c := Smooth.FieldExtensionReflection.fieldSpecMap_surjective φ
  have hres : FormallyUnramified (pullback.snd f a) :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @FormallyUnramified) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (IsPullback.of_hasPullback (pullback.snd f a) c).flip
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ ht
  have hs := mem_properUnramifiedBaseOpen_of_residueFiber f s hres
  rintro _ ⟨k, rfl⟩
  have hk : b k = s := congrArg b (Subsingleton.elim k (IsLocalRing.closedPoint K))
  exact hk.symm ▸ hs

theorem properUnramifiedBaseOpen_all_tests
    {T : Scheme.{u}} (b : T ⟶ S) :
    Set.range b ⊆ properUnramifiedBaseOpen f ↔
      FormallyUnramified (pullback.snd f b) := by
  refine ⟨unramified_pullback_of_range_subset f b, fun hb => ?_⟩
  let := hb
  rintro _ ⟨t, rfl⟩
  let c := T.fromSpecResidueField t
  have hiter : FormallyUnramified (pullback.snd (pullback.snd f b) c) :=
    MorphismProperty.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback (pullback.snd f b) c) hb
  have hcomp : FormallyUnramified (pullback.snd f (c ≫ b)) := by
    let e := pullbackLeftPullbackSndIso f b c
    have he : e.inv ≫ pullback.snd (pullback.snd f b) c = pullback.snd f (c ≫ b) := by
      rw [← pullbackLeftPullbackSndIso_hom_snd f b c]
      exact e.inv_hom_id_assoc _
    have hh : FormallyUnramified (e.inv ≫ pullback.snd (pullback.snd f b) c) :=
      MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance hiter
    exact he ▸ hh
  have hr := (properUnramifiedBaseOpen_field_point f (c ≫ b)).mpr hcomp
  let k : Spec (T.residueField t) := (⊥ : PrimeSpectrum (T.residueField t))
  have hk := hr ⟨k, rfl⟩
  change b (T.fromSpecResidueField t k) ∈ (properUnramifiedBaseOpen f : Set S) at hk
  change b t ∈ (properUnramifiedBaseOpen f : Set S)
  simpa only [Scheme.fromSpecResidueField_apply] using hk

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.UnramifiedBaseOpen
