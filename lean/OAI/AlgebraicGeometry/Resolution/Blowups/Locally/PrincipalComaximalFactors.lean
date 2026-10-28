import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalRegular

/-! # Principal Comaximal Factors -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Locally

noncomputable section

/-! Local principality descends over open covers and passes to comaximal factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.of_openCover {X : Scheme} (I : X.IdealSheafData)
    (C : X.OpenCover) (hlocal : ∀ i, PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap (C.f i))) :
    PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf I := by
  intro x
  obtain ⟨i, y, hy⟩ := C.exists_eq x
  obtain ⟨W, hyW, r, hr⟩ := hlocal i y
  let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  let j := W.2.fromSpec ≫ C.f i
  have he : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {r}) := by
    rw [Scheme.IdealSheafData.comap_comp, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, hr]
  refine ⟨Affine.OpenBoundaryTransport.Construction.specOpenImage Γ(C.X i, W) j, ?_, (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv Γ(C.X i, W) j).symm r,
    Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_equation Γ(C.X i, W) j I r he⟩
  rw [Affine.OpenBoundaryTransport.Construction.specOpenImage_eq_opensRange]
  have hyr : y ∈ W.2.fromSpec.opensRange := by rw [W.2.opensRange_fromSpec]; exact hyW
  obtain ⟨z, hz⟩ := hyr
  exact ⟨z, (congrArg (C.f i) hz).trans hy⟩

theorem PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.comaximal_left_factor
    {X : Scheme} (K L : X.IdealSheafData) (hKL : K ⊔ L = ⊤)
    (hlocal : PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (K * L)) : PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf K := by
  let U : Bool → X.Opens := fun b => if b then K.support.compl else L.support.compl
  let C : X.OpenCover := Scheme.Cover.mkOfCovers Bool (fun b => U b)
    (fun b => (U b).ι) (by
      intro x
      by_cases hx : x ∈ K.support
      · have hy := Global.ResidualNeighborhood.Construction.idealSheaf_support_subset_complement_of_sup_top K L hKL hx
        exact ⟨false, ⟨⟨x, hy⟩, rfl⟩⟩
      · exact ⟨true, ⟨⟨x, hx⟩, rfl⟩⟩) (fun _ => inferInstance)
  apply PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.of_openCover K C
  intro b
  change Bool at b
  cases b with
  | false =>
      have h := hlocal.comap (U false).ι
      change PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (K.comap (U false).ι)
      have ht : L.comap (U false).ι = ⊤ := Global.ResidualNeighborhood.Construction.idealSheaf_comap_supportComplement_eq_top L
      rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, ht] at h
      simpa only [← Scheme.IdealSheafData.one_eq_top, mul_one] using h
  | true =>
      change PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (K.comap (Scheme.Opens.ι (X := X) K.support.compl))
      rw [Global.ResidualNeighborhood.Construction.idealSheaf_comap_supportComplement_eq_top]
      exact PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.top _

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Locally
