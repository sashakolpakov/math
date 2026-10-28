import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterDividedMembership
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenBoundaryTransport

/-! # Atlas From Affine Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Native global common-center atlases from actual affine charts and quotient-kernel identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem AtlasFromAffineCover.Construction.specOpenSectionEquiv_ideal_map_symm {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData) (K : Ideal R)
    (hI : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K) :
    I.ideal (Affine.OpenBoundaryTransport.Construction.specOpenImage R j) = K.map (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv R j).symm.toRingHom := by
  rw [Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_ideal R j I K hI]
  exact (Ideal.map_symm (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv R j)).symm

def CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofAffineCover
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData) {β : Type}
    (D : β → X.IdealSheafData) (C : X.AffineOpenCover) [∀ i, Algebra ℂ (C.X i)]
    (hstructure : ∀ i, C.f i ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (C.X i))
    (K : ∀ i, Ideal (C.X i)) (w : ∀ i, β → C.X i) (F : C.I₀ → Finset β)
    (hI : ∀ i, I.comap (C.f i) = Affine.QuotientKernel.Construction.affineQuotientKernel (K i))
    (hD : ∀ i j, (D j).comap (C.f i) = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i j}))
    (hboundary : ∀ i, LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (C.X i) (w i))
    (hcenter : ∀ i, MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts ℂ (C.X i) (K i) (w i) (F i)) :
    CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D := by
  let U (i : C.I₀) := Affine.OpenBoundaryTransport.Construction.specOpenImage (C.X i) (C.f i)
  let : ∀ i, Algebra ℂ Γ(X, U i) := fun i => Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (U i)
  let e (i : C.I₀) : Γ(X, U i) ≃ₐ[ℂ] C.X i := Affine.OpenBoundaryTransport.Construction.specOpenSectionAlgEquiv f (C.X i) (C.f i) (hstructure i)
  let v (i : C.I₀) : β → Γ(X, U i) := fun j => (e i).symm (w i j)
  have he (i : C.I₀) : I.ideal (U i) = (K i).map (e i).symm.toRingHom :=
    AtlasFromAffineCover.Construction.specOpenSectionEquiv_ideal_map_symm (C.X i) (C.f i) I (K i) (hI i)
  have hc (i : C.I₀) : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts ℂ (.of Γ(X, U i)) (I.ideal (U i)) (v i) (F i) := by
    rw [he i]
    exact (hcenter i).etale_baseChange (S := .of Γ(X, U i)) (e i).symm.toAlgHom
      (RingHom.Etale.of_bijective (e i).symm.bijective)
  refine { indices := C.I₀
           opens := U
           cover := ?_
           equations := v
           component := ?_
           divided := F
           contained := ?_
           boundary := ?_
           center := hc }
  · simp only [U, Affine.OpenBoundaryTransport.Construction.specOpenImage_eq_opensRange]
    exact C.openCover.iSup_opensRange
  · intro i j
    exact Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_equation (C.X i) (C.f i) (D j) (w i j) (hD i j)
  · intro i j hj
    exact (hc i).divided_mem (I.ideal (U i)) j hj
  · intro i
    exact (hboundary i).etale_baseChange (S := .of Γ(X, U i)) (e i).symm.toAlgHom
      (RingHom.Etale.of_bijective (e i).symm.bijective)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
