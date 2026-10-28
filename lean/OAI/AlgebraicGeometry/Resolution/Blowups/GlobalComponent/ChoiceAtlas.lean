import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.ChoiceGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceOpenCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas

/-! # Choice Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.ChoiceAtlas.Construction

noncomputable section

/-! Finite actual affine atlases for the canonical global coefficient-component stage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure GlobalComponentChoiceAtlas {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (J : X.IdealSheafData) (n : ℕ) where
  indices : Type
  finite : Fintype indices
  rings : indices → CommRingCat
  algebra : ∀ i, Algebra ℂ (rings i)
  rational : ∀ i, Algebra ℚ (rings i)
  smooth : ∀ i, Algebra.Smooth ℂ (rings i)
  map : ∀ i, Spec (rings i) ⟶ X
  isOpenImmersion : ∀ i, IsOpenImmersion (map i)
  quasiCompact : ∀ i, QuasiCompact (map i)
  ground : ∀ i, map i ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (rings i)
  cover : ⨆ i, (map i).opensRange = ⊤
  ideals : ∀ i, Ideal (rings i)
  ideal_eq : ∀ i, J.comap (map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (ideals i)
  choice : ∀ i, Component.CenterChoice.Construction.ComponentCenterChoice ℂ (rings i) (ideals i) n

attribute [instance] GlobalComponentChoiceAtlas.finite GlobalComponentChoiceAtlas.algebra
  GlobalComponentChoiceAtlas.rational GlobalComponentChoiceAtlas.smooth
  GlobalComponentChoiceAtlas.isOpenImmersion GlobalComponentChoiceAtlas.quasiCompact

theorem GlobalComponentChoiceAtlas.existsUnique_center {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {n : ℕ} (A : GlobalComponentChoiceAtlas f J n) :
    ∃! I : X.IdealSheafData, ∀ i, I.comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (A.choice i).center :=
  ChoiceGluing.Construction.existsUnique_global_component_choice_center ℂ f A.rings A.map A.ground A.cover J
    A.ideals A.ideal_eq n A.choice

theorem exists_finite_native_affine_cover (X : Scheme) [CompactSpace X] :
    ∃ s : Finset X.affineOpens, (⨆ U : s, U.val.val) = ⊤ := by
  classical
  have hcover : Set.univ ⊆ ⋃ U : X.affineOpens, (U.val : Set X) := by
    intro x _
    have hx : x ∈ ⨆ U : X.affineOpens, U.val := by rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨U, hU⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => (U.val : Set X)) (fun U => U.val.isOpen) hcover
  refine ⟨s, top_le_iff.mp ?_⟩
  intro x _
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩

theorem exists_global_component_choice_atlas_of_affine_cover
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤)
    {κ : Type} [Fintype κ] (U : κ → X.affineOpens) (hU : ⨆ i, (U i).val = ⊤) :
    Nonempty (GlobalComponentChoiceAtlas f J n) := by
  classical
  let : ∀ i, Algebra ℂ Γ(X, U i) := fun i => Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (U i)
  let : ∀ i, Algebra.Smooth ℂ Γ(X, U i) := fun i => Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f (U i)
  have hex (i : κ) := Component.ChoiceOpenCover.Construction.exists_finite_component_choice_cover ℂ (J.ideal (U i)) n
    (show Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (J.ideal (U i)) (n + 1) = ⊤ from
      congrArg (fun K : X.IdealSheafData => K.ideal (U i)) hbound)
  choose p s hs hc using hex
  let ι := (i : κ) × p i
  let R (i : ι) : CommRingCat := .of (Localization.Away (s i.1 i.2))
  let : ∀ i : ι, Algebra ℂ (R i) := fun _ => inferInstance
  let : ∀ i : ι, Algebra ℚ (R i) := fun i => ((algebraMap ℂ (R i)).comp (algebraMap ℚ ℂ)).toAlgebra
  let : ∀ i : ι, Algebra.Smooth ℂ (R i) := fun i => by
    let : Algebra.Smooth Γ(X, U i.1) (R i) := Algebra.Smooth.of_isLocalization_Away (s i.1 i.2)
    exact Algebra.Smooth.comp ℂ Γ(X, U i.1) (R i)
  let : ∀ i : ι, IsNoetherianRing (R i) := fun i => Algebra.FiniteType.isNoetherianRing ℂ (R i)
  let j (i : ι) : Spec (R i) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U i.1) (R i))) ≫ (U i.1).2.fromSpec
  let : ∀ i, IsOpenImmersion (j i) := fun i => by
    let : IsOpenImmersion (U i.1).2.fromSpec := (U i.1).2.isOpenImmersion_fromSpec
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U i.1) (R i)))) :=
      IsOpenImmersion.of_isLocalization (s i.1 i.2)
    exact inferInstanceAs (IsOpenImmersion (_ ≫ _))
  have hj (i : ι) : j i ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (R i) := by
    dsimp only [j]
    rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f (U i.1), ← Spec.map_comp]
    rfl
  have hcover : ⨆ i, (j i).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨i, y, hy⟩ := Global.MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec U hU x
    have hymem : y ∈ ⨆ a : p i, PrimeSpectrum.basicOpen (s i a) := by rw [hs i]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hymem
    obtain ⟨q, hq⟩ := Etale.RefinementHelpers.Construction.exists_localization_away_prime (s i a) y ha
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨⟨i, a⟩, ?_⟩
    change x ∈ Set.range (j ⟨i, a⟩)
    refine ⟨q, ?_⟩
    change (U i).2.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, U i) (R ⟨i, a⟩)) q) = x
    rw [hq]
    exact hy
  refine ⟨{
    indices := ι
    finite := inferInstance
    rings := R
    algebra := fun i => inferInstance
    rational := fun i => inferInstance
    smooth := fun i => inferInstance
    map := j
    isOpenImmersion := fun i => inferInstance
    quasiCompact := fun i => inferInstance
    ground := hj
    cover := hcover
    ideals := fun i => (J.ideal (U i.1)).map (algebraMap Γ(X, U i.1) (R i))
    ideal_eq := fun i => Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel J (U i.1)
      (algebraMap Γ(X, U i.1) (R i))
    choice := fun i => (hc i.1 i.2).some }⟩

theorem exists_global_component_choice_atlas
    {X : Scheme} [CompactSpace X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (n : ℕ) (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤) :
    Nonempty (GlobalComponentChoiceAtlas f J n) := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_native_affine_cover X
  exact exists_global_component_choice_atlas_of_affine_cover f J n hbound (fun U : s => U.val) hs

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.ChoiceAtlas.Construction
