import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineOpenNilLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ThickeningOpens

/-! # Lift Overlap -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftOverlap

noncomputable section

/-! The overlap maps between actual nilpotent lifts of etale charts.
They are constructed by the etale lifting property; no overlap maps
or cocycle identities are prescribed as extra data. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X₀ X Y₀ : Scheme.{u}} (i : X₀ ⟶ X) (f₀ : Y₀ ⟶ X₀)

structure Chart where
  base : Scheme.{u}
  base_affine : IsAffine base
  baseMap : base ⟶ X
  base_open : IsOpenImmersion baseMap
  scheme : Scheme.{u}
  affine : IsAffine scheme
  map : scheme ⟶ base
  etale : Etale map
  reduced : Scheme.{u}
  reduction : reduced ⟶ scheme
  closed : IsClosedImmersion reduction
  surjective : Surjective reduction
  nilpotent : IsNilpotent reduction.ker
  source : reduced ⟶ Y₀
  source_open : IsOpenImmersion source
  over : reduction ≫ map ≫ baseMap = source ≫ f₀ ≫ i

attribute [instance] Chart.base_affine Chart.base_open Chart.affine Chart.etale
  Chart.closed Chart.surjective Chart.source_open

namespace Chart
variable {i f₀} (A B C : Chart i f₀)

abbrev toBase : A.scheme ⟶ X := A.map ≫ A.baseMap
instance toBase_etale : Etale A.toBase := inferInstanceAs (Etale (A.map ≫ A.baseMap))

def overlap : A.scheme.Opens :=
  Closed.ThickeningOpens.liftOpen A.reduction (A.source ⁻¹ᵁ B.source.opensRange)

def point (x : A.scheme) : Y₀ :=
  A.source ((Closed.ThickeningOpens.homeomorph A.reduction).symm x)

@[simp] theorem point_reduction (x : A.reduced) : A.point (A.reduction x) = A.source x := by
  change A.source ((Closed.ThickeningOpens.homeomorph A.reduction).symm
    (Closed.ThickeningOpens.homeomorph A.reduction x)) = _
  rw [Homeomorph.symm_apply_apply]

theorem mem_overlap_iff (x : A.scheme) : x ∈ A.overlap B ↔ A.point x ∈ Set.range B.source := Iff.rfl

instance reduction_restrict_surjective (U : A.scheme.Opens) : Surjective (A.reduction ∣_ U) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict A.reduction U).flip
    (inferInstanceAs (Surjective A.reduction))

@[simp] theorem reduction_mem_overlap (x : A.reduced) :
    A.reduction x ∈ A.overlap B ↔ A.source x ∈ Set.range B.source := by
  change x ∈ A.reduction ⁻¹ᵁ Closed.ThickeningOpens.liftOpen A.reduction
    (A.source ⁻¹ᵁ B.source.opensRange) ↔ _
  rw [Closed.ThickeningOpens.preimage_liftOpen]
  rfl

theorem residue_range :
    Set.range ((A.reduction ⁻¹ᵁ A.overlap B).ι ≫ A.source) ⊆ Set.range B.source := by
  rintro _ ⟨x, rfl⟩
  have hx := x.2
  change x.1 ∈ A.reduction ⁻¹ᵁ Closed.ThickeningOpens.liftOpen A.reduction
    (A.source ⁻¹ᵁ B.source.opensRange) at hx
  rw [Closed.ThickeningOpens.preimage_liftOpen] at hx
  exact hx

def residueMap : (A.reduction ⁻¹ᵁ A.overlap B).toScheme ⟶ B.reduced :=
  IsOpenImmersion.lift B.source ((A.reduction ⁻¹ᵁ A.overlap B).ι ≫ A.source) (A.residue_range B)

@[reassoc] theorem residueMap_source : A.residueMap B ≫ B.source =
    (A.reduction ⁻¹ᵁ A.overlap B).ι ≫ A.source := IsOpenImmersion.lift_fac _ _ _

theorem overlap_square :
    (A.residueMap B ≫ B.reduction) ≫ B.toBase =
      (A.reduction ∣_ A.overlap B) ≫ (A.overlap B).ι ≫ A.toBase := by
  rw [Category.assoc, B.over, ← Category.assoc, Chart.residueMap_source]
  rw [← Category.assoc (A.reduction ∣_ A.overlap B), morphismRestrict_ι]
  simp only [Category.assoc, A.over]

private theorem transition_exists : ∃ l : (A.overlap B).toScheme ⟶ B.scheme,
    (A.reduction ∣_ A.overlap B) ≫ l = A.residueMap B ≫ B.reduction ∧
      l ≫ B.toBase = (A.overlap B).ι ≫ A.toBase := by
  exact (AffineOpenNilLift.existsUnique_lift B.map B.baseMap
    (A.reduction ∣_ A.overlap B)
    (NilpotentOpenRestriction.nilpotent A.reduction A.nilpotent _)
    (A.residueMap B ≫ B.reduction) ((A.overlap B).ι ≫ A.toBase)
    (A.overlap_square B)).exists

def transition : (A.overlap B).toScheme ⟶ B.scheme := ((transition_exists A) B).choose

@[reassoc] theorem transition_reduction :
    (A.reduction ∣_ A.overlap B) ≫ A.transition B = A.residueMap B ≫ B.reduction :=
  ((transition_exists A) B).choose_spec.1

@[reassoc] theorem transition_base : A.transition B ≫ B.toBase = (A.overlap B).ι ≫ A.toBase :=
  ((transition_exists A) B).choose_spec.2

theorem point_transition (x : (A.overlap B).toScheme) :
    B.point (A.transition B x) = A.point ((A.overlap B).ι x) := by
  obtain ⟨x₀, rfl⟩ := (A.reduction ∣_ A.overlap B).surjective x
  have ht := congrArg (fun g : (A.reduction ⁻¹ᵁ A.overlap B).toScheme ⟶ B.scheme => g x₀)
    (A.transition_reduction B)
  have hi := congrArg (fun g : (A.reduction ⁻¹ᵁ A.overlap B).toScheme ⟶ A.scheme => g x₀)
    (morphismRestrict_ι A.reduction (A.overlap B))
  change A.transition B ((A.reduction ∣_ A.overlap B) x₀) = B.reduction (A.residueMap B x₀) at ht
  change (A.overlap B).ι ((A.reduction ∣_ A.overlap B) x₀) =
    A.reduction ((A.reduction ⁻¹ᵁ A.overlap B).ι x₀) at hi
  rw [ht, hi, point_reduction, point_reduction]
  exact congrArg (fun g : (A.reduction ⁻¹ᵁ A.overlap B).toScheme ⟶ Y₀ => g x₀)
    (A.residueMap_source B)

theorem transition_range : Set.range (A.transition B) ⊆ (B.overlap A : Set B.scheme) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨x₀, rfl⟩ := (A.reduction ∣_ A.overlap B).surjective x
  have ht := congrArg (fun g : (A.reduction ⁻¹ᵁ A.overlap B).toScheme ⟶ B.scheme => g x₀)
    (A.transition_reduction B)
  change A.transition B ((A.reduction ∣_ A.overlap B) x₀) = B.reduction (A.residueMap B x₀) at ht
  rw [ht]
  apply (B.reduction_mem_overlap A _).2
  refine ⟨(A.reduction ⁻¹ᵁ A.overlap B).ι x₀, ?_⟩
  exact (congrArg (fun g : (A.reduction ⁻¹ᵁ A.overlap B).toScheme ⟶ Y₀ => g x₀)
    (A.residueMap_source B)).symm

def transitionOpen : (A.overlap B).toScheme ⟶ (B.overlap A).toScheme :=
  IsOpenImmersion.lift (B.overlap A).ι (A.transition B)
    (by simpa only [Scheme.Opens.range_ι] using A.transition_range B)

@[reassoc] theorem transitionOpen_ι : A.transitionOpen B ≫ (B.overlap A).ι = A.transition B :=
  IsOpenImmersion.lift_fac _ _ _

/-- Reduction of a transition on any test scheme, expressed using the
original source charts. This is the normalization needed for inverses
and triple-overlap identities. -/
theorem transition_reduction_of {Z Z₀ : Scheme.{u}} (j : Z₀ ⟶ Z)
    (u : Z ⟶ (A.overlap B).toScheme) (v : Z₀ ⟶ A.reduced) (w : Z₀ ⟶ B.reduced)
    (hv : j ≫ u ≫ (A.overlap B).ι = v ≫ A.reduction)
    (hw : v ≫ A.source = w ≫ B.source) :
    j ≫ u ≫ A.transition B = w ≫ B.reduction := by
  let hp := isPullback_morphismRestrict A.reduction (A.overlap B)
  let l := hp.lift (j ≫ u) v (by simpa only [Category.assoc] using hv)
  have hl : l ≫ A.residueMap B = w := by
    apply (cancel_mono B.source).mp
    rw [Category.assoc, Chart.residueMap_source, ← Category.assoc, hp.lift_snd]
    exact hw
  calc
    _ = l ≫ (A.reduction ∣_ A.overlap B) ≫ A.transition B := by
      simpa only [Category.assoc] using
        (congrArg (fun q => q ≫ A.transition B) (hp.lift_fst (j ≫ u) v
          (by simpa only [Category.assoc] using hv))).symm
    _ = l ≫ A.residueMap B ≫ B.reduction := by rw [Chart.transition_reduction]
    _ = _ := by rw [← Category.assoc, hl]

theorem transitionOpen_inv : A.transitionOpen B ≫ B.transitionOpen A = 𝟙 _ := by
  apply (cancel_mono (A.overlap B).ι).mp
  rw [Category.assoc, transitionOpen_ι, Category.id_comp]
  apply FormallyUnramified.hom_ext (A.reduction ∣_ A.overlap B)
    (NilpotentOpenRestriction.nilpotent A.reduction A.nilpotent _) A.toBase
  · have h := B.transition_reduction_of A (A.reduction ∣_ A.overlap B)
      (A.transitionOpen B) (A.residueMap B) (A.reduction ⁻¹ᵁ A.overlap B).ι
      (by rw [transitionOpen_ι, Chart.transition_reduction]) (A.residueMap_source B)
    simpa only [Category.assoc, morphismRestrict_ι] using h
  · rw [Category.assoc, Chart.transition_base, ← Category.assoc, transitionOpen_ι, Chart.transition_base]

def transitionIso : (A.overlap B).toScheme ≅ (B.overlap A).toScheme where
  hom := A.transitionOpen B
  inv := B.transitionOpen A
  hom_inv_id := A.transitionOpen_inv B
  inv_hom_id := B.transitionOpen_inv A

instance transitionOpen_isIso : IsIso (A.transitionOpen B) := (A.transitionIso B).isIso_hom

theorem overlap_self : A.overlap A = ⊤ := by
  ext x
  obtain ⟨y, rfl⟩ := A.reduction.surjective x
  change A.reduction y ∈ A.overlap A ↔ True
  exact iff_true_intro ((A.reduction_mem_overlap A y).2 ⟨y, rfl⟩)

theorem transition_self : A.transition A = (A.overlap A).ι := by
  apply FormallyUnramified.hom_ext (A.reduction ∣_ A.overlap A)
    (NilpotentOpenRestriction.nilpotent A.reduction A.nilpotent _) A.toBase
  · rw [Chart.transition_reduction, morphismRestrict_ι]
    have h : A.residueMap A = (A.reduction ⁻¹ᵁ A.overlap A).ι := by
      apply (cancel_mono A.source).mp
      exact A.residueMap_source A
    rw [h]
  · exact A.transition_base A

theorem transitionOpen_self : A.transitionOpen A = 𝟙 _ := by
  apply (cancel_mono (A.overlap A).ι).mp
  rw [transitionOpen_ι, transition_self, Category.id_comp]

end Chart

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftOverlap
