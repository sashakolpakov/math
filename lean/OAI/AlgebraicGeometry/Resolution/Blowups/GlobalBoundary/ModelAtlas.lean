import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Smooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelOrderEquiv

/-! # Model Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Compact native normal-crossing boundaries admit finite affine covers with explicit étale coordinate models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {β : Type}
    (D : β → X.IdealSheafData) where
  indices : Type
  finite : Fintype indices
  rings : indices → CommRingCat
  algebra : ∀ i, Algebra ℂ (rings i)
  map : ∀ i, Spec (rings i) ⟶ X
  isOpenImmersion : ∀ i, IsOpenImmersion (map i)
  quasiCompact : ∀ i, QuasiCompact (map i)
  ground : ∀ i, map i ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (rings i)
  cover : ⨆ i, (map i).opensRange = ⊤
  equations : ∀ i, β → rings i
  component : ∀ i j, (D j).comap (map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {equations i j})
  model : ∀ i, Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ (rings i) β (equations i)

attribute [instance] GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.finite GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.algebra
  GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.isOpenImmersion GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.quasiCompact

theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.exists_modelAtlas
    {X : Scheme} [CompactSpace X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {β : Type} {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) : Nonempty (GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) := by
  classical
  let : ∀ i, Algebra ℂ Γ(X, A.opens i) := fun i => Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  let κ := (i : A.indices) × PrimeSpectrum Γ(X, A.opens i)
  let C (p : κ) := Classical.choice (A.boundary p.1 p.2)
  let j (p : κ) : Spec (C p).carrier ⟶ X :=
    Spec.map (CommRingCat.ofHom (C p).map.toRingHom) ≫ (A.opens p.1).2.fromSpec
  let : ∀ p, IsOpenImmersion (j p) := fun p => by
    let : IsOpenImmersion (A.opens p.1).2.fromSpec := (A.opens p.1).2.isOpenImmersion_fromSpec
    exact inferInstanceAs (IsOpenImmersion (_ ≫ _))
  have hall : Set.univ ⊆ ⋃ p : κ, ((j p).opensRange : Set X) := by
    intro x _
    obtain ⟨i, q, hq⟩ := Global.MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec A.opens A.cover x
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, q⟩, (C ⟨i, q⟩).point, ?_⟩
    change (A.opens i).2.fromSpec (PrimeSpectrum.comap (C ⟨i, q⟩).map.toRingHom (C ⟨i, q⟩).point) = x
    rw [(C ⟨i, q⟩).point_over]
    exact hq
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p : κ => ((j p).opensRange : Set X)) (fun p => (j p).opensRange.isOpen) hall
  have hcover : ⨆ p : s, (j p.val).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hx⟩
  have hg (p : κ) : j p ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (C p).carrier := by
    dsimp only [j]
    rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f (A.opens p.1), ← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact (C p).map.commutes c
  refine ⟨{
    indices := s
    finite := inferInstance
    rings := fun p => (C p.val).carrier
    algebra := fun p => (C p.val).algebra
    map := fun p => j p.val
    isOpenImmersion := fun p => inferInstance
    quasiCompact := fun p => inferInstance
    ground := fun p => hg p.val
    cover := hcover
    equations := fun p l => (C p.val).map (A.equations p.val.1 l)
    component := ?_
    model := fun p => (C p.val).model }⟩
  intro p l
  change (D l).comap (Spec.map (CommRingCat.ofHom (C p.val).map.toRingHom) ≫ (A.opens p.val.1).2.fromSpec) = _
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel, A.component, Ideal.map_span, Set.image_singleton]

def GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.affineIdeal
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} {D : β → X.IdealSheafData}
    (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (i : A.indices) : Ideal (A.rings i) :=
  (Affine.KernelOrderEquiv.Construction.exists_affineQuotientKernel (J.comap (A.map i))).choose

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.affineIdeal_eq
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} {D : β → X.IdealSheafData}
    (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (i : A.indices) :
    J.comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (A.affineIdeal J i) :=
  (Affine.KernelOrderEquiv.Construction.exists_affineQuotientKernel (J.comap (A.map i))).choose_spec.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
