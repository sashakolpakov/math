import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.TransverseCoordinateFiber
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.Schedule

/-! # Closed Carrier Boundary Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.ClosedCarrierBoundaryAtlas.Construction

noncomputable section

/-! Native boundary atlases on actual closed coefficient carriers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

local instance {X : Scheme} (H : X.IdealSheafData) (U : X.affineOpens) :
    IsOpenImmersion (H.subschemeCover.f U) := H.subschemeCover.openCover.map_prop U

theorem exists_point_on_subscheme_chosen_cover {X : Scheme} (H : X.IdealSheafData)
    {ι : Type} (U : ι → X.affineOpens) (hcover : ⨆ i, (U i).1 = ⊤) (x : H.subscheme) :
    ∃ i, x ∈ (H.subschemeCover.f (U i)).opensRange := by
  have hx : H.subschemeι x ∈ ⨆ i, (U i).1 := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨i, ?_⟩
  rw [H.opensRange_subschemeCover_map]
  exact hi

def subschemeChosenAffineCover {X : Scheme.{0}} (H : X.IdealSheafData)
    {ι : Type} (U : ι → X.affineOpens) (hcover : ⨆ i, (U i).1 = ⊤) : H.subscheme.AffineOpenCover where
  I₀ := ι
  X i := .of (Γ(X, U i) ⧸ H.ideal (U i))
  f i := H.subschemeCover.f (U i)
  map_prop i := H.subschemeCover.openCover.map_prop (U i)
  idx x := (exists_point_on_subscheme_chosen_cover H U hcover x).choose
  covers x := (exists_point_on_subscheme_chosen_cover H U hcover x).choose_spec

theorem subschemeChart_over_affine {X : Scheme} (H : X.IdealSheafData) (U : X.affineOpens) :
    H.subschemeCover.f U ≫ H.subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (H.ideal U))) ≫ U.2.fromSpec :=
  (Scheme.IdealSheafData.subschemeCover_map_subschemeι H U).trans (Category.assoc _ _ _)

def _root_.OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.closedCarrier
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} [Fintype β]
    {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (H : X.IdealSheafData)
    (hboundary : ∀ i, letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
      LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of (Γ(X, A.opens i) ⧸ H.ideal (A.opens i)))
        (fun j => Ideal.Quotient.mk (H.ideal (A.opens i)) (A.equations i j))) :
    MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (H.subschemeι ≫ f) (fun j => (D j).comap H.subschemeι) [Finset.univ] := by
  let C := subschemeChosenAffineCover H A.opens A.cover
  let : ∀ i, Algebra ℂ Γ(X, A.opens i) := fun i => Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  let : ∀ i : C.I₀, Algebra ℂ (C.X i) := fun i => by
    change A.indices at i
    let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
    exact inferInstanceAs (Algebra ℂ (Γ(X, A.opens i) ⧸ H.ideal (A.opens i)))
  let w (i : C.I₀) (j : β) : C.X i := Ideal.Quotient.mk (H.ideal (A.opens i)) (A.equations i j)
  apply MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.ofAffineCover (H.subschemeι ≫ f)
    (fun j => (D j).comap H.subschemeι) [Finset.univ] C _ w _ hboundary
    (fun i => Boundary.Schedule.Construction.boundaryFacesCover_univ (w i))
  · intro i
    change A.indices at i
    change H.subschemeCover.f (A.opens i) ≫ (H.subschemeι ≫ f) = _
    rw [← Category.assoc, subschemeChart_over_affine]
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (H.ideal (A.opens i)))) ≫
      (A.opens i).2.fromSpec) ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (Γ(X, A.opens i) ⧸ H.ideal (A.opens i))
    rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f (A.opens i), ← Spec.map_comp]
    rfl
  · intro i j
    change A.indices at i
    change ((D j).comap H.subschemeι).comap (H.subschemeCover.f (A.opens i)) = _
    rw [← Scheme.IdealSheafData.comap_comp, subschemeChart_over_affine]
    exact (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel (D j) (A.opens i)
      (Ideal.Quotient.mk (H.ideal (A.opens i)))).trans (by
        rw [A.component, Ideal.map_span, Set.image_singleton]
        rfl)

/-- A displayed transverse coordinate for the carrier restricts every
boundary label to an actual normal-crossing atlas on that carrier. -/
def _root_.OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.transverseClosedCarrier
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} [Fintype β]
    {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (H : X.IdealSheafData)
    (M : ∀ i, letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
      Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ Γ(X, A.opens i) β (A.equations i))
    (z : ∀ i, letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i); (M i).indices)
    (hz : ∀ i, letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i); ∀ j, (M i).coordinate j ≠ some (z i))
    (hH : ∀ i, letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
      H.ideal (A.opens i) = Ideal.span {(M i).map (MvPolynomial.X (z i))}) :
    MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (H.subschemeι ≫ f) (fun j => (D j).comap H.subschemeι) [Finset.univ] := by
  apply A.closedCarrier H
  intro i
  let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  have he := congrArg (fun K : Ideal Γ(X, A.opens i) =>
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of (Γ(X, A.opens i) ⧸ K))
      (fun j => Ideal.Quotient.mk K (A.equations i j))) (hH i)
  exact he.mpr ((M i).transverseCoordinateFiber (z i) (hz i)).hasEtaleBoundaryCharts

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.ClosedCarrierBoundaryAtlas.Construction
