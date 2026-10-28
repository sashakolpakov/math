import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenBoundaryTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialTerminal
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialUnitGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CenterSmooth
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Monomial Boundary Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas.Construction

noncomputable section

/-! Native affine atlases carrying global labelled boundaries and the common monomial schedule faces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure GlobalMonomialBoundaryAtlas {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {β : Type}
    (D : β → X.IdealSheafData) (L : List (Finset β)) where
  indices : Type
  opens : indices → X.affineOpens
  cover : ⨆ i, (opens i).1 = ⊤
  equations : ∀ i, β → Γ(X, opens i)
  component : ∀ i j, (D j).ideal (opens i) = Ideal.span {equations i j}
  boundary : ∀ i, letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (opens i)
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of Γ(X, opens i)) (equations i)
  faces : ∀ i, Boundary.Schedule.Construction.BoundaryFacesCover (equations i) L

def GlobalMonomialBoundaryAtlas.ofAffineCover
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {β : Type} (D : β → X.IdealSheafData)
    (L : List (Finset β)) (C : X.AffineOpenCover) [∀ i, Algebra ℂ (C.X i)]
    (hstructure : ∀ i, C.f i ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (C.X i))
    (w : ∀ i, β → C.X i)
    (hD : ∀ i j, (D j).comap (C.f i) = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i j}))
    (hboundary : ∀ i, LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (C.X i) (w i))
    (hfaces : ∀ i, Boundary.Schedule.Construction.BoundaryFacesCover (w i) L) : GlobalMonomialBoundaryAtlas f D L := by
  let U (i : C.I₀) := Affine.OpenBoundaryTransport.Construction.specOpenImage (C.X i) (C.f i)
  have hcover : ⨆ i, (U i).1 = ⊤ := by
    simp only [U, Affine.OpenBoundaryTransport.Construction.specOpenImage_eq_opensRange]
    exact C.openCover.iSup_opensRange
  have hex (i : C.I₀) :
      letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (U i)
      ∃ v : β → Γ(X, U i),
        (∀ j, (D j).ideal (U i) = Ideal.span {v j}) ∧
        LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of Γ(X, U i)) v ∧ Boundary.Schedule.Construction.BoundaryFacesCover v L :=
    Affine.OpenBoundaryTransport.Construction.exists_native_affine_boundary_equations f (C.X i) (C.f i) (hstructure i)
      D (w i) L (hD i) (hboundary i) (hfaces i)
  choose v hv hb hf using hex
  exact ⟨C.I₀, U, hcover, v, hv, hb, hf⟩

theorem exists_point_on_chosen_affine_spec
    {X : Scheme} {ι : Type} (U : ι → X.affineOpens) (hcover : ⨆ i, (U i).1 = ⊤) (x : X) :
    ∃ i, x ∈ Set.range (U i).2.fromSpec := by
  let : ∀ i, IsOpenImmersion (U i).2.fromSpec := fun i => (U i).2.isOpenImmersion_fromSpec
  have hx : x ∈ ⨆ i, (U i).1 := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨i, ?_⟩
  change x ∈ (U i).2.fromSpec.opensRange
  rw [(U i).2.opensRange_fromSpec]
  exact hi

def chosenAffineSpecCover {X : Scheme} {ι : Type} (U : ι → X.affineOpens)
    (hcover : ⨆ i, (U i).1 = ⊤) : X.AffineOpenCover where
  I₀ := ι
  X i := Γ(X, U i)
  f i := (U i).2.fromSpec
  map_prop i := (U i).2.isOpenImmersion_fromSpec
  idx x := (exists_point_on_chosen_affine_spec U hcover x).choose
  covers x := (exists_point_on_chosen_affine_spec U hcover x).choose_spec

theorem GlobalMonomialBoundaryAtlas.monomial_terminal
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (L : List (Finset β)) (A : GlobalMonomialBoundaryAtlas f D L)
    (a : β → ℕ) (b : ℕ) (hb : 0 < b) (hbound : ∀ S ∈ L, Boundary.MonomialSchedule.Construction.boundaryFaceWeight a S < b) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (MixedBoundary.Construction.boundaryMonomialSheaf D a) (b - 1) = ⊤ := by
  apply DifferentialUnitGluing.Construction.idealSheaf_eq_top_of_openCover _ (chosenAffineSpecCover A.opens A.cover).openCover
  intro i
  change A.indices at i
  let : IsOpenImmersion (A.opens i).2.fromSpec := (A.opens i).2.isOpenImmersion_fromSpec
  let : Algebra ℂ Γ(X, A.opens i) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  let : Algebra.Smooth ℂ Γ(X, A.opens i) := (A.boundary i).smooth
  have hterminal := (A.faces i).monomial_terminal (A.boundary i) a b hb hbound
  have hJ : (MixedBoundary.Construction.boundaryMonomialSheaf D a).comap (A.opens i).2.fromSpec =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (A.equations i) a}) := by
    rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel,
      MixedBoundary.Construction.boundaryMonomialSheaf_local_equations D a (A.opens i) (A.equations i) (A.component i)]
  exact DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_unit_on_affine f (MixedBoundary.Construction.boundaryMonomialSheaf D a) (b - 1)
    (A.opens i).2.fromSpec (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f (A.opens i)).symm
    (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (A.equations i) a}) hJ hterminal

theorem idealSheaf_complex_center_smooth_on_affine_chart
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData) (U : X.affineOpens)
    (h : letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U; Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U)) :
    Smooth (I.subschemeCover.f U ≫ (I.subschemeι ≫ f)) := by
  rw [← Category.assoc, Scheme.IdealSheafData.subschemeCover_map_subschemeι]
  change Smooth (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫
    U.2.isoSpec.inv) ≫ U.1.ι) ≫ f)
  rw [Category.assoc]
  change Smooth ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.fromSpec) ≫ f)
  rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U, ← Spec.map_comp]
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr h)

theorem idealSheaf_complex_center_smooth_of_chosen_affine_cover
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {ι : Type} (U : ι → X.affineOpens) (hcover : ⨆ i, (U i).1 = ⊤)
    (h : ∀ i, letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (U i); Algebra.Smooth ℂ (Γ(X, U i) ⧸ I.ideal (U i))) :
    Smooth (I.subschemeι ≫ f) := by
  let : ∀ i, IsOpenImmersion (I.subschemeCover.f (U i)) :=
    fun i => I.subschemeCover.openCover.map_prop (U i)
  have hsource : ⨆ i, (I.subschemeCover.f (U i)).opensRange = ⊤ := by
    simp_rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  let : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun i => (I.subschemeCover.f (U i)).opensRange) hsource
  intro i
  let : Smooth (I.subschemeCover.f (U i) ≫ (I.subschemeι ≫ f)) :=
    idealSheaf_complex_center_smooth_on_affine_chart f I (U i) (h i)
  exact SupportedBlowupSmoothGluing.Construction.smooth_on_opensRange_of_open_immersion (I.subschemeι ≫ f) (I.subschemeCover.f (U i))

theorem GlobalMonomialBoundaryAtlas.intersection_smooth
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {β : Type}
    (D : β → X.IdealSheafData) (L : List (Finset β)) (A : GlobalMonomialBoundaryAtlas f D L)
    (C : Finset β) : Smooth ((GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C).subschemeι ≫ f) := by
  apply idealSheaf_complex_center_smooth_of_chosen_affine_cover f _ A.opens A.cover
  intro i
  let : Algebra ℂ Γ(X, A.opens i) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  rw [GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf_local_equations D C (A.opens i) (A.equations i)
    (fun j _ => A.component i j)]
  exact (A.boundary i).intersection_smooth C

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas.Construction
