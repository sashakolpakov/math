import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Blowup Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BlowupRestriction.Construction

noncomputable section

/-! Compatibility of the affine blowup diagram with restrictions of the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Localization compatibility with a separately specified extended ideal. -/
theorem affineBlowupMapTo_localization_isPullback
    [IsDomain R] [IsNoetherianRing R] (I : Ideal R) (J : Ideal S)
    (s : R) [IsLocalization.Away s S] (h : I.map (algebraMap R S) = J)
    (hI : I ≠ ⊥) (hs : s ≠ 0) :
    IsPullback (Functor.Construction.affineBlowupMapTo I J (algebraMap R S) h)
      (ReesGrading.Construction.affineBlowupToSpec J) (ReesGrading.Construction.affineBlowupToSpec I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  subst J
  exact BaseChange.Construction.affineBlowup_localization_isPullback I s hI hs

variable {X : Scheme.{u}}

/-- The diagram of affine blowups is cartesian on every nonempty principal
restriction of an integral Noetherian base. -/
theorem idealBlowup_basicOpen_isPullback
    [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData)
    {U V : X.affineOpens} [Nonempty V.1] (hUV : U ≤ V)
    (s : Γ(X, V)) (hU : U.1 = X.basicOpen s) (hI : I.ideal V ≠ ⊥) (hs : s ≠ 0) :
    IsPullback ((Functor.Construction.idealBlowupFunctor I).map (homOfLE hUV))
      ((Functor.Construction.idealBlowupNatTrans I).app U) ((Functor.Construction.idealBlowupNatTrans I).app V)
      (X.homOfLE hUV) := by
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  let : Algebra Γ(X, V) Γ(X, U) := (Functor.Construction.affineRestriction hUV).toAlgebra
  let : IsLocalization.Away s Γ(X, U) :=
    V.2.isLocalization_of_eq_basicOpen s (homOfLE hUV) hU
  have hpb := affineBlowupMapTo_localization_isPullback
    (I.ideal V) (I.ideal U) s (Functor.Construction.affineRestriction_ideal I hUV) hI hs
  have hbase : IsPullback (Spec.map (CommRingCat.ofHom (Functor.Construction.affineRestriction hUV)))
      U.2.isoSpec.inv V.2.isoSpec.inv (X.homOfLE hUV) :=
    IsPullback.of_vert_isIso ⟨Functor.Construction.affineRestriction_over hUV⟩
  exact hpb.paste_vert hbase

/-- Local pullback charts over the source base detect whether a comparison
map is an open immersion. -/
theorem isOpenImmersion_of_local_base_charts
    {B B' V U : Scheme.{u}} (i : B' ⟶ B) (p : B ⟶ V) (p' : B' ⟶ U)
    (j : U ⟶ V) [IsOpenImmersion j] (h : i ≫ p = p' ≫ j)
    (hloc : ∀ y : U, ∃ (T W : Scheme.{u}) (k : T ⟶ B') (q : T ⟶ W) (w : W ⟶ U),
      IsOpenImmersion w ∧ IsPullback k q p' w ∧ y ∈ Set.range w ∧
        IsOpenImmersion (k ≫ i)) :
    IsOpenImmersion i := by
  have hinj : Function.Injective i := by
    intro x₁ x₂ hx
    have hy : p' x₁ = p' x₂ := by
      apply j.injective
      have hp := congrArg p hx
      change (i ≫ p) x₁ = (i ≫ p) x₂ at hp
      rw [h] at hp
      exact hp
    obtain ⟨T, W, k, q, w, _, hpb, ⟨y, hy₁⟩, hki⟩ := hloc (p' x₁)
    let : IsOpenImmersion (k ≫ i) := hki
    obtain ⟨z₁, hz₁, _⟩ := Scheme.exists_preimage_of_isPullback hpb x₁ y hy₁.symm
    obtain ⟨z₂, hz₂, _⟩ := Scheme.exists_preimage_of_isPullback hpb x₂ y (hy₁.trans hy).symm
    have hz : z₁ = z₂ := (k ≫ i).injective (by
      simpa only [Scheme.Hom.comp_apply, hz₁, hz₂] using hx)
    exact hz₁.symm.trans ((congrArg k hz).trans hz₂)
  apply IsOpenImmersion.of_forall_source_exists i hinj
  intro x
  obtain ⟨T, W, k, q, w, hw, hpb, ⟨y, hy⟩, hki⟩ := hloc (p' x)
  let : IsOpenImmersion w := hw
  let hk : IsOpenImmersion k := MorphismProperty.of_isPullback hpb.flip hw
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback hpb x y hy.symm
  exact ⟨T, k, hk, ⟨z, hz⟩, hki⟩

/-- A nonzero ideal on an affine open remains nonzero on any smaller
nonempty affine open of an integral scheme. -/
theorem ideal_ne_bot_on_smaller_open [IsIntegral X] (I : X.IdealSheafData)
    {U V : X.affineOpens} [Nonempty U.1] (hUV : U ≤ V) (hI : I.ideal V ≠ ⊥) :
    I.ideal U ≠ ⊥ := by
  rw [← Functor.Construction.affineRestriction_ideal I hUV]
  exact (Ideal.map_eq_bot_iff_of_injective
    (map_injective_of_isIntegral X (homOfLE (X := X.Opens) hUV))).not.mpr hI

/-- Restriction between arbitrary nonempty affine opens induces an open
immersion between their blowups. -/
theorem idealBlowup_map_isOpenImmersion
    [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData)
    {U V : X.affineOpens} [Nonempty U.1] [Nonempty V.1]
    (hUV : U ≤ V) (hI : I.ideal V ≠ ⊥) :
    IsOpenImmersion ((Functor.Construction.idealBlowupFunctor I).map (homOfLE hUV)) := by
  have hIU := ideal_ne_bot_on_smaller_open I hUV hI
  refine @isOpenImmersion_of_local_base_charts
    (ReesGrading.Construction.affineBlowup (I.ideal V)) (ReesGrading.Construction.affineBlowup (I.ideal U)) V.1 U.1
    ((Functor.Construction.idealBlowupFunctor I).map (homOfLE hUV))
    (ReesGrading.Construction.affineBlowupToSpec (I.ideal V) ≫ V.2.isoSpec.inv)
    (ReesGrading.Construction.affineBlowupToSpec (I.ideal U) ≫ U.2.isoSpec.inv)
    (X.homOfLE hUV) inferInstance ((Functor.Construction.idealBlowupNatTrans I).naturality (homOfLE hUV)) ?_
  intro y
  obtain ⟨f, g, e, hy⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y.1 ⟨y.2, hUV y.2⟩
  have hf : f ≠ 0 := by
    intro hf
    rw [hf, Scheme.basicOpen_zero] at hy
    exact hy
  have hg : g ≠ 0 := by
    intro hg
    rw [e, hg, Scheme.basicOpen_zero] at hy
    exact hy
  let W : X.affineOpens := X.affineBasicOpen f
  have hWU : W ≤ U := X.basicOpen_le f
  have hWV : W ≤ V := hWU.trans hUV
  have hpU := idealBlowup_basicOpen_isPullback I hWU f rfl hIU hf
  have hpV := idealBlowup_basicOpen_isPullback I hWV g e hI hg
  refine ⟨(Functor.Construction.idealBlowupFunctor I).obj W, W.1,
    (Functor.Construction.idealBlowupFunctor I).map (homOfLE hWU), (Functor.Construction.idealBlowupNatTrans I).app W,
    X.homOfLE hWU, inferInstance, hpU,
    ⟨⟨y.1, hy⟩, Scheme.homOfLE_apply' hWU y.1 hy⟩, ?_⟩
  have hk : IsOpenImmersion ((Functor.Construction.idealBlowupFunctor I).map (homOfLE hWV)) :=
    MorphismProperty.of_isPullback hpV.flip
      (inferInstance : IsOpenImmersion (X.homOfLE (U := W.1) (V := V.1) hWV))
  exact ((Functor.Construction.idealBlowupFunctor I).map_comp (homOfLE hWU) (homOfLE hUV)) ▸ hk

/-- Affine blowups of a nonzero ideal sheaf commute with arbitrary
inclusions between nonempty affine opens. -/
theorem idealBlowup_affineOpen_isPullback
    [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData)
    {U V : X.affineOpens} [Nonempty U.1] [Nonempty V.1]
    (hUV : U ≤ V) (hI : I.ideal V ≠ ⊥) :
    IsPullback ((Functor.Construction.idealBlowupFunctor I).map (homOfLE hUV))
      ((Functor.Construction.idealBlowupNatTrans I).app U) ((Functor.Construction.idealBlowupNatTrans I).app V)
      (X.homOfLE hUV) := by
  have hIU := ideal_ne_bot_on_smaller_open I hUV hI
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  let : IsIntegral (ReesGrading.Construction.affineBlowup (I.ideal U)) := Cover.Construction.affineBlowup_integral (I.ideal U) hIU
  let : IsIntegral (ReesGrading.Construction.affineBlowup (I.ideal V)) := Cover.Construction.affineBlowup_integral (I.ideal V) hI
  let hi : IsOpenImmersion ((Functor.Construction.idealBlowupFunctor I).map (homOfLE hUV)) :=
    idealBlowup_map_isOpenImmersion I hUV hI
  exact @BaseChange.Construction.isPullback_of_proper_open_diagram
    (ReesGrading.Construction.affineBlowup (I.ideal V)) (ReesGrading.Construction.affineBlowup (I.ideal U)) V.1 U.1
    inferInstance inferInstance
    (ReesGrading.Construction.affineBlowupToSpec (I.ideal V) ≫ V.2.isoSpec.inv) inferInstance
    (X.homOfLE hUV) inferInstance
    (ReesGrading.Construction.affineBlowupToSpec (I.ideal U) ≫ U.2.isoSpec.inv) inferInstance
    ((Functor.Construction.idealBlowupFunctor I).map (homOfLE hUV)) hi
    ((Functor.Construction.idealBlowupNatTrans I).naturality (homOfLE hUV))

/-- A commutative square over an empty open base is cartesian. -/
theorem isPullback_of_empty_open_base
    {B B' V U : Scheme.{u}} [IsEmpty U] (i : B' ⟶ B) (p : B ⟶ V) (p' : B' ⟶ U)
    (j : U ⟶ V) [IsOpenImmersion j] (h : i ≫ p = p' ≫ j) :
    IsPullback i p' p j := by
  let : IsEmpty B' := (fun x : B' => p' x).isEmpty
  let : IsOpenImmersion i := inferInstance
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback p' i j p h
  apply TopologicalSpace.Opens.ext
  change p ⁻¹' (Set.range j) = Set.range i
  ext x
  constructor
  · rintro ⟨u, _⟩
    exact isEmptyElim u
  · rintro ⟨b, _⟩
    exact isEmptyElim b

/-- A nonzero ideal sheaf on an integral scheme is nonzero on every
nonempty affine open. -/
theorem nonzero_idealSheaf_on_affineOpen [IsIntegral X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (U : X.affineOpens) [Nonempty U.1] :
    I.ideal U ≠ ⊥ := by
  intro hIU
  apply hI
  apply Scheme.IdealSheafData.ext
  funext V
  change I.ideal V = ⊥
  by_contra hIV
  obtain ⟨r, _, hr⟩ := (Submodule.ne_bot_iff (I.ideal V)).mp hIV
  let : Nontrivial Γ(X, V) := nontrivial_of_ne r 0 hr
  let : Nonempty V.1 := Nonempty.map V.2.isoSpec.inv inferInstance
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.1.isOpen V.1.isOpen
    (by simpa using (inferInstance : Nonempty U.1))
    (by simpa using (inferInstance : Nonempty V.1))
  obtain ⟨f, g, e, hx⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  let W : X.affineOpens := X.affineBasicOpen f
  let : Nonempty W.1 := ⟨⟨x, hx⟩⟩
  have hWU : W ≤ U := X.basicOpen_le f
  have hWV : W ≤ V := by
    change X.basicOpen f ≤ V.1
    rw [e]
    exact X.basicOpen_le g
  have hIW := ideal_ne_bot_on_smaller_open I hWV hIV
  have hmap := Functor.Construction.affineRestriction_ideal I hWU
  rw [hIU, Ideal.map_bot] at hmap
  exact hIW hmap.symm

/-- All affine-open transition squares of the blowup of a nonzero ideal
sheaf on an integral locally Noetherian scheme are cartesian. -/
theorem idealBlowupNatTrans_equifibered
    [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    (Functor.Construction.idealBlowupNatTrans I).Equifibered := by
  intro U V h
  by_cases hU : Nonempty U.1
  · let : Nonempty U.1 := hU
    let : Nonempty V.1 := Nonempty.map (X.homOfLE (leOfHom h)) hU
    exact idealBlowup_affineOpen_isPullback I (leOfHom h)
      (nonzero_idealSheaf_on_affineOpen I hI V)
  · let : IsEmpty U.1 := not_nonempty_iff.mp hU
    exact @isPullback_of_empty_open_base
      (ReesGrading.Construction.affineBlowup (I.ideal V)) (ReesGrading.Construction.affineBlowup (I.ideal U)) V.1 U.1 inferInstance
      ((Functor.Construction.idealBlowupFunctor I).map h)
      (ReesGrading.Construction.affineBlowupToSpec (I.ideal V) ≫ V.2.isoSpec.inv)
      (ReesGrading.Construction.affineBlowupToSpec (I.ideal U) ≫ U.2.isoSpec.inv)
      (X.homOfLE (leOfHom h)) inferInstance ((Functor.Construction.idealBlowupNatTrans I).naturality h)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BlowupRestriction.Construction
