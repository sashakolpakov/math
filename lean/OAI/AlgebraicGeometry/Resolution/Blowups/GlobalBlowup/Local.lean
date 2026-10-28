import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.DisjointCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BlowupLift
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Nonzero
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalRegular
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas

/-! # Local -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Local.Construction

noncomputable section

section

/-! Uniqueness of actual global blowup lifts from the dense complement of the center. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem idealSheaf_supportComplement_nonempty {X : Scheme} [IsReduced X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) : (I.support.compl : Set X).Nonempty := by
  apply Set.nonempty_compl.mpr
  intro h
  exact hI (Scheme.IdealSheafData.support_eq_top_iff.mp (SetLike.coe_injective h))

theorem idealSheaf_supportComplement_dense {X : Scheme} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) : Dense (I.support.compl : Set X) :=
  I.support.compl.isOpen.dense (idealSheaf_supportComplement_nonempty I hI)

theorem globalBlowup_hom_ext_of_dense_complement
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsReduced Y]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (q : Y ⟶ X)
    (hd : Dense ((q ⁻¹ᵁ I.support.compl : Y.Opens) : Set Y))
    (g₁ g₂ : Y ⟶ Data.Construction.globalBlowup I hI)
    (h₁ : g₁ ≫ Data.Construction.globalBlowupToBase I hI = q) (h₂ : g₂ ≫ Data.Construction.globalBlowupToBase I hI = q) : g₁ = g₂ := by
  let U : X.Opens := I.support.compl
  let W : Y.Opens := q ⁻¹ᵁ U
  let : IsDominant W.ι := Opens.isDominant_ι hd
  let : IsIso (Data.Construction.globalBlowupToBase I hI ∣_ U) := Blowup.Complement.Construction.globalBlowup_supportComplement_isIso I hI
  let : IsIso (pullback.snd (Data.Construction.globalBlowupToBase I hI) U.ι) :=
    Blowup.DisjointCenter.Construction.isIso_pullback_snd_of_isIso_on_open (Data.Construction.globalBlowupToBase I hI) U.ι U
      (by rintro x ⟨y, rfl⟩; exact y.property)
  apply Blowup.BlowupLift.Construction.hom_eq_of_dense_isIso_baseChange (Data.Construction.globalBlowupToBase I hI) U.ι W.ι g₁ g₂
    (h₁.trans h₂.symm) (q ∣_ U)
  rw [h₁]
  exact (morphismRestrict_ι q U).symm

theorem globalBlowup_hom_ext
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (q : Y ⟶ X) (hIq : I.comap q ≠ ⊥)
    (g₁ g₂ : Y ⟶ Data.Construction.globalBlowup I hI)
    (h₁ : g₁ ≫ Data.Construction.globalBlowupToBase I hI = q) (h₂ : g₂ ≫ Data.Construction.globalBlowupToBase I hI = q) : g₁ = g₂ := by
  apply globalBlowup_hom_ext_of_dense_complement I hI q _ g₁ g₂ h₁ h₂
  have h := idealSheaf_supportComplement_dense (I.comap q) hIq
  rw [Scheme.IdealSheafData.support_comap] at h
  exact h

end

section

/-! Actual local lifts to the global Rees blowup from a nonzero locally principal pulled-back center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem locallyPrincipal_regular_generators_within
    {Y : Scheme} [IsIntegral Y] (I : Y.IdealSheafData) (hI : I ≠ ⊥)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf I) (O : Y.Opens) (y : Y) (hy : y ∈ O) :
    ∃ (W : Y.affineOpens), y ∈ W.1 ∧ W.1 ≤ O ∧
      ∃ r : Γ(Y, W), IsRegular r ∧ I.ideal W = Ideal.span {r} := by
  obtain ⟨U, hyU, r, hr⟩ := hlocal y
  obtain ⟨W, hW, hyW, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (U := U.1 ⊓ O) (x := y) ⟨hyU, hy⟩
  let A : Y.affineOpens := ⟨W, hW⟩
  have hAU : A ≤ U := hsub.trans inf_le_left
  let s := Blowup.Functor.Construction.affineRestriction hAU r
  have hs : I.ideal A = Ideal.span {s} := Locally.PrincipalIdealSheaf.Construction.principal_idealSheaf_restrict I hAU r hr
  let : Nonempty A.1 := ⟨⟨y, hyW⟩⟩
  have hs0 : s ≠ 0 := by
    intro h
    apply Blowup.BlowupRestriction.Construction.nonzero_idealSheaf_on_affineOpen I hI A
    rw [hs, h, Ideal.span_singleton_eq_bot.mpr rfl]
  exact ⟨A, hyW, hsub.trans inf_le_right, s, IsRegular.of_ne_zero hs0, hs⟩

theorem exists_local_globalBlowup_lift
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (q : Y ⟶ X)
    (hIq : I.comap q ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap q)) (y : Y) :
    ∃ (W : Y.affineOpens), y ∈ W.1 ∧
      ∃ l : Spec Γ(Y, W) ⟶ Data.Construction.globalBlowup I hI,
        l ≫ Data.Construction.globalBlowupToBase I hI = W.2.fromSpec ≫ q := by
  obtain ⟨U, hU, hqy, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := q y) trivial
  let A : X.affineOpens := ⟨U, hU⟩
  obtain ⟨W, hyW, hWA, r, hr, he⟩ := locallyPrincipal_regular_generators_within
    (I.comap q) hIq hlocal (q ⁻¹ᵁ A.1) y hqy
  let φ := (q.appLE A.1 W.1 hWA).hom
  have hgen : (I.ideal A).map φ = Ideal.span {r} :=
    (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I q A W hWA).symm.trans he
  let a : (I.ideal A).map φ := ⟨r, hgen ▸ Ideal.subset_span (Set.mem_singleton r)⟩
  refine ⟨W, hyW, Blowup.BlowupLift.Construction.affineBlowupLift (I.ideal A) φ a hgen hr ≫ Data.Construction.globalBlowupChart I hI A, ?_⟩
  rw [Category.assoc, Data.Construction.globalBlowupChart_over, ← Category.assoc, Blowup.BlowupLift.Construction.affineBlowupLift_over]
  exact IsAffineOpen.SpecMap_appLE_fromSpec q A.2 W.2 hWA

end

/-! The actual global Rees blowup has the universal lifting property for integral sources with nonzero locally principal center pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem globalBlowup_lifts_agree_on_open_overlap
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (q : Y ⟶ X) (hIq : I.comap q ≠ ⊥)
    {V W : Scheme} (j : V ⟶ Y) (k : W ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion k]
    (a : V ⟶ Data.Construction.globalBlowup I hI) (b : W ⟶ Data.Construction.globalBlowup I hI)
    (ha : a ≫ Data.Construction.globalBlowupToBase I hI = j ≫ q)
    (hb : b ≫ Data.Construction.globalBlowupToBase I hI = k ≫ q) :
    pullback.fst j k ≫ a = pullback.snd j k ≫ b := by
  let t := pullback.fst j k ≫ j
  let : IsReduced (pullback j k) := isReduced_of_isOpenImmersion t
  have hd : Dense ((q ⁻¹ᵁ I.support.compl : Y.Opens) : Set Y) := by
    have h := idealSheaf_supportComplement_dense (I.comap q) hIq
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h
  apply globalBlowup_hom_ext_of_dense_complement I hI (t ≫ q)
    (hd.preimage t.isOpenEmbedding.isOpenMap) (pullback.fst j k ≫ a) (pullback.snd j k ≫ b)
  · rw [Category.assoc, ha]
    exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, hb]
    exact (pullback.condition_assoc (f := j) (g := k) q).symm.trans
      (Category.assoc _ _ _).symm

theorem existsUnique_globalBlowup_lift
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (q : Y ⟶ X)
    (hIq : I.comap q ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap q)) :
    ∃! l : Y ⟶ Data.Construction.globalBlowup I hI, l ≫ Data.Construction.globalBlowupToBase I hI = q := by
  have hex := exists_local_globalBlowup_lift I hI q hIq hlocal
  choose W hW l hl using hex
  let : ∀ y, IsOpenImmersion (W y).2.fromSpec := fun y => (W y).2.isOpenImmersion_fromSpec
  let C : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec Γ(Y, W y))
    (fun y => (W y).2.fromSpec) (by
      intro y
      refine ⟨y, ?_⟩
      change y ∈ (W y).2.fromSpec.opensRange
      rw [(W y).2.opensRange_fromSpec]
      exact hW y) (fun _ => inferInstance)
  have hcompat (y z : C.I₀) : pullback.fst (C.f y) (C.f z) ≫ l y =
      pullback.snd (C.f y) (C.f z) ≫ l z :=
    globalBlowup_lifts_agree_on_open_overlap I hI q hIq (C.f y) (C.f z) (l y) (l z) (hl y) (hl z)
  let g := C.glueMorphisms l hcompat
  have hg : g ≫ Data.Construction.globalBlowupToBase I hI = q := by
    apply C.hom_ext
    intro y
    rw [← Category.assoc, C.ι_glueMorphisms l hcompat y]
    exact hl y
  exact ⟨g, hg, fun a ha => globalBlowup_hom_ext I hI q hIq a g ha hg⟩

def globalBlowupUniversalLift
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (q : Y ⟶ X)
    (hIq : I.comap q ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap q)) :
    Y ⟶ Data.Construction.globalBlowup I hI :=
  (existsUnique_globalBlowup_lift I hI q hIq hlocal).choose

theorem globalBlowupUniversalLift_over
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (q : Y ⟶ X)
    (hIq : I.comap q ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap q)) :
    globalBlowupUniversalLift I hI q hIq hlocal ≫ Data.Construction.globalBlowupToBase I hI = q :=
  (existsUnique_globalBlowup_lift I hI q hIq hlocal).choose_spec.1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Local.Construction
