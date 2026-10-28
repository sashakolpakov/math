import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BlowupRestriction

/-! # Data -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Data.Construction

noncomputable section

/-! The global blowup obtained by gluing the actual affine Rees blowups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (I : X.IdealSheafData) (hI : I ≠ ⊥)

/-- The proved cartesian affine blowup diagram supplies genuine gluing data. -/
def blowupGluingData : X.directedAffineCover.RelativeGluingData where
  functor := Blowup.Functor.Construction.idealBlowupFunctor I
  natTrans := Blowup.Functor.Construction.idealBlowupNatTrans I
  equifibered := Blowup.BlowupRestriction.Construction.idealBlowupNatTrans_equifibered I hI

/-- Blowup along a nonzero ideal sheaf of an integral locally Noetherian scheme. -/
abbrev globalBlowup : Scheme.{u} := (blowupGluingData I hI).glued

/-- The morphism from the glued blowup to its base scheme. -/
def globalBlowupToBase : globalBlowup I hI ⟶ X := (blowupGluingData I hI).toBase

/-- Every affine Rees blowup is an open chart of the global blowup. -/
def globalBlowupChart (U : X.affineOpens) : ReesGrading.Construction.affineBlowup (I.ideal U) ⟶ globalBlowup I hI :=
  (blowupGluingData I hI).cover.f U

instance globalBlowupChart_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion (globalBlowupChart I hI U) := by
  exact (blowupGluingData I hI).cover.map_prop U

theorem globalBlowupChart_over (U : X.affineOpens) :
    globalBlowupChart I hI U ≫ globalBlowupToBase I hI =
      ReesGrading.Construction.affineBlowupToSpec (I.ideal U) ≫ U.2.fromSpec := by
  exact ((blowupGluingData I hI).ι_toBase U).trans (Category.assoc _ _ _)

/-- The global blowup restricts to the affine Rees blowup on each affine open. -/
theorem globalBlowup_affineOpen_isPullback (U : X.affineOpens) :
    IsPullback (globalBlowupChart I hI U)
      (ReesGrading.Construction.affineBlowupToSpec (I.ideal U) ≫ U.2.isoSpec.inv)
      (globalBlowupToBase I hI) U.1.ι :=
  ((blowupGluingData I hI).isPullback_natTrans_ι_toBase U).flip

/-- The glued blowup is proper over its base. -/
instance globalBlowupToBase_isProper : IsProper (globalBlowupToBase I hI) := by
  apply IsZariskiLocalAtTarget.of_openCover X.directedAffineCover
  intro U
  change X.affineOpens at U
  change IsProper (pullback.snd (globalBlowupToBase I hI) U.1.ι)
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  rw [← (globalBlowup_affineOpen_isPullback I hI U).isoPullback_inv_snd]
  infer_instance

/-- The global blowup is reduced because all its affine Rees blowups are reduced. -/
instance globalBlowup_isReduced : AlgebraicGeometry.IsReduced (globalBlowup I hI) := by
  let 𝒰 := (blowupGluingData I hI).cover
  let : ∀ U : 𝒰.I₀, AlgebraicGeometry.IsReduced (𝒰.X U) := by
    intro U
    change AlgebraicGeometry.IsReduced (ReesGrading.Construction.affineBlowup (I.ideal U))
    infer_instance
  exact AlgebraicGeometry.IsReduced.of_openCover (globalBlowup I hI) 𝒰

/-- The maps into the glued scheme agree on every affine restriction. -/
theorem globalBlowupChart_transition {U V : X.affineOpens} (hUV : U ≤ V) :
    (Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hUV) ≫ globalBlowupChart I hI V =
      globalBlowupChart I hI U :=
  colimit.w (blowupGluingData I hI).functor (homOfLE hUV)

/-- The image of any nonempty affine blowup chart is irreducible. -/
theorem globalBlowupChart_range_irreducible (U : X.affineOpens) [Nonempty U.1] :
    IsIrreducible (Set.range (globalBlowupChart I hI U)) := by
  let : IsIntegral (ReesGrading.Construction.affineBlowup (I.ideal U)) :=
    Blowup.Cover.Construction.affineBlowup_integral (I.ideal U) (Blowup.BlowupRestriction.Construction.nonzero_idealSheaf_on_affineOpen I hI U)
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (ReesGrading.Construction.affineBlowup (I.ideal U))).image
    (globalBlowupChart I hI U) (globalBlowupChart I hI U).continuous.continuousOn

/-- Any two nonempty affine blowup charts have nonempty intersection in the
global blowup. -/
theorem globalBlowupChart_ranges_inter (U V : X.affineOpens)
    [Nonempty U.1] [Nonempty V.1] :
    (Set.range (globalBlowupChart I hI U) ∩ Set.range (globalBlowupChart I hI V)).Nonempty := by
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.1.isOpen V.1.isOpen
    (by simpa using (inferInstance : Nonempty U.1))
    (by simpa using (inferInstance : Nonempty V.1))
  obtain ⟨f, g, e, hx⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  let W : X.affineOpens := X.affineBasicOpen f
  let : Nonempty W.1 := ⟨⟨x, hx⟩⟩
  let : IsIntegral (ReesGrading.Construction.affineBlowup (I.ideal W)) :=
    Blowup.Cover.Construction.affineBlowup_integral (I.ideal W) (Blowup.BlowupRestriction.Construction.nonzero_idealSheaf_on_affineOpen I hI W)
  have hWU : W ≤ U := X.basicOpen_le f
  have hWV : W ≤ V := by
    change X.basicOpen f ≤ V.1
    rw [e]
    exact X.basicOpen_le g
  let z : ReesGrading.Construction.affineBlowup (I.ideal W) := Nonempty.some inferInstance
  refine ⟨globalBlowupChart I hI W z,
    ⟨(Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hWU) z, ?_⟩,
    ⟨(Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hWV) z, ?_⟩⟩
  · change ((Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hWU) ≫ globalBlowupChart I hI U) z = _
    rw [globalBlowupChart_transition]
    rfl
  · change ((Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hWV) ≫ globalBlowupChart I hI V) z = _
    rw [globalBlowupChart_transition]
    rfl

/-- Every nonempty affine blowup chart is dense in the global blowup. -/
theorem globalBlowupChart_dense (U : X.affineOpens) [Nonempty U.1] :
    Dense (Set.range (globalBlowupChart I hI U)) := by
  intro x
  obtain ⟨V, z, rfl⟩ := (blowupGluingData I hI).cover.exists_eq x
  change X.affineOpens at V
  let : Nonempty V.1 := ⟨(ReesGrading.Construction.affineBlowupToSpec (I.ideal V) ≫ V.2.isoSpec.inv) z⟩
  have hV := globalBlowupChart_range_irreducible I hI V
  have hUV := globalBlowupChart_ranges_inter I hI V U
  have hsub := subset_closure_inter_of_isPreirreducible_of_isOpen hV.2
    (globalBlowupChart I hI U).opensRange.isOpen hUV
  exact closure_mono Set.inter_subset_right (hsub ⟨z, rfl⟩)

/-- The global blowup of an integral scheme along a nonzero ideal sheaf is irreducible. -/
instance globalBlowup_irreducible : IrreducibleSpace (globalBlowup I hI) := by
  let x : X := Nonempty.some inferInstance
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  let V : X.affineOpens := ⟨U, hU⟩
  let : Nonempty V.1 := ⟨⟨x, hx⟩⟩
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (globalBlowup I hI))
  rw [← (globalBlowupChart_dense I hI V).closure_eq]
  exact (globalBlowupChart_range_irreducible I hI V).closure

instance globalBlowup_integral : IsIntegral (globalBlowup I hI) := by
  exact isIntegral_of_irreducibleSpace_of_isReduced (globalBlowup I hI)

/-- A base localization avoiding the center maps openly into the global blowup. -/
def globalBlowupComplementMap (U : X.affineOpens) (a : I.ideal U) :
    Spec (.of (Localization.Away a.val)) ⟶ globalBlowup I hI :=
  Blowup.Localization.Construction.affineBlowupComplementMap (I.ideal U) a ≫ globalBlowupChart I hI U

instance globalBlowupComplementMap_isOpenImmersion (U : X.affineOpens) (a : I.ideal U) :
    IsOpenImmersion (globalBlowupComplementMap I hI U a) := by
  unfold globalBlowupComplementMap
  infer_instance

theorem globalBlowupComplementMap_over (U : X.affineOpens) (a : I.ideal U) :
    globalBlowupComplementMap I hI U a ≫ globalBlowupToBase I hI =
      Blowup.Localization.Construction.baseLocalizationMap a.val ≫ U.2.fromSpec := by
  unfold globalBlowupComplementMap
  rw [Category.assoc, globalBlowupChart_over, ← Category.assoc, Blowup.Localization.Construction.affineBlowupComplementMap_over]

/-- The global blowup is birational, compatibly with its actual structural morphism. -/
theorem globalBlowup_partialIso :
    ∃ e : (globalBlowup I hI).PartialIso X,
      e.source.ι ≫ globalBlowupToBase I hI = e.iso.hom ≫ e.target.ι := by
  let x : X := Nonempty.some inferInstance
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  let V : X.affineOpens := ⟨U, hU⟩
  let : Nonempty V.1 := ⟨⟨x, hx⟩⟩
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff (I.ideal V)).mp
    (Blowup.BlowupRestriction.Construction.nonzero_idealSheaf_on_affineOpen I hI V)
  let aI : I.ideal V := ⟨a, ha⟩
  let : IsDomain (Localization.Away a) := Localization.Away.isDomain ha0
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  let : IsOpenImmersion (Blowup.Localization.Construction.baseLocalizationMap a ≫ V.2.fromSpec) := by
    infer_instance
  exact Blowup.Birational.Construction.compatible_partialIso_of_common_open
    (globalBlowupComplementMap I hI V aI) (Blowup.Localization.Construction.baseLocalizationMap a ≫ V.2.fromSpec)
    (globalBlowupToBase I hI) (globalBlowupComplementMap_over I hI V aI)

theorem globalBlowup_birational : Scheme.Birational (globalBlowup I hI) X := by
  obtain ⟨e, _⟩ := globalBlowup_partialIso I hI
  exact ⟨e⟩

/-- Over a localization avoiding the center, the global blowup is an isomorphism. -/
theorem globalBlowup_localization_isIso (U : X.affineOpens) [Nonempty U.1]
    (a : I.ideal U) (ha : a.val ≠ 0) :
    IsIso (pullback.snd (globalBlowupToBase I hI) (Blowup.Localization.Construction.baseLocalizationMap a.val ≫ U.2.fromSpec)) := by
  let : IsDomain (Localization.Away a.val) := Localization.Away.isDomain ha
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let : IsOpenImmersion (Blowup.Localization.Construction.baseLocalizationMap a.val ≫ U.2.fromSpec) := by
    infer_instance
  exact Blowup.Birational.Construction.isIso_pullback_snd_of_open_section
    (globalBlowupToBase I hI) (Blowup.Localization.Construction.baseLocalizationMap a.val ≫ U.2.fromSpec)
    (globalBlowupComplementMap I hI U a) (globalBlowupComplementMap_over I hI U a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Data.Construction
