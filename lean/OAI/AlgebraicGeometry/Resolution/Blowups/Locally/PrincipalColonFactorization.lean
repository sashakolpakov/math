import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Factorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelOrderEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas

/-! # Principal Colon Factorization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalColonFactorization.Construction

noncomputable section

/-! Native principal ideal quotients factor exactly, with exact affine pullback when the divisor stays regular. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem locallyPrincipal_noetherianIdealSheafColon_factorization
    {X : Scheme.{0}} [IsLocallyNoetherian X] (J K : X.IdealSheafData)
    (hK : PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf K) (hJ : J ≤ K) :
    K * NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon J K = J := by
  choose U hx r hr using hK
  have hcover : ⨆ x : X, (U x).1 = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (Global.MonomialBoundaryAtlas.Construction.chosenAffineSpecCover U hcover).openCover
  intro x
  change X at x
  change (K * NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon J K).comap (U x).2.fromSpec = J.comap (U x).2.fromSpec
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel]
  apply congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
  change K.ideal (U x) * (J.ideal (U x)).colon (K.ideal (U x) : Set Γ(X, U x)) = J.ideal (U x)
  rw [hr x]
  exact ControlledTransform.Construction.principal_mul_colon_of_le _ _ ((hJ (U x)).trans (hr x).le)

theorem idealSheaf_factorization_comap_regular_affine
    {X : Scheme.{0}} (J K L : X.IdealSheafData) (hfactor : K * L = J)
    (R : CommRingCat) (j : Spec R ⟶ X) (A : Ideal R) (c : R)
    (hJ : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel A)
    (hK : K.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {c})) (hc : IsRegular c) :
    L.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (A.colon (Ideal.span {c} : Set R)) := by
  obtain ⟨B, hB⟩ := Affine.KernelOrderEquiv.Construction.exists_affineQuotientKernel (L.comap j)
  have he := congrArg (fun I : X.IdealSheafData => I.comap j) hfactor
  rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, hJ, hK, ← hB, ← IdealSheaf.ProductRestriction.Construction.affineQuotientKernel_mul] at he
  have hring := (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp he
  rw [← hB, ← hring, ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular B c hc]

theorem locallyPrincipal_colon_comap_regular_affine
    {X : Scheme.{0}} [IsLocallyNoetherian X] (J K : X.IdealSheafData)
    (hlocal : PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf K) (hdiv : J ≤ K)
    (R : CommRingCat) (j : Spec R ⟶ X) (A : Ideal R) (c : R)
    (hJ : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel A)
    (hK : K.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {c})) (hc : IsRegular c) :
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon J K).comap j =
      Affine.QuotientKernel.Construction.affineQuotientKernel (A.colon (Ideal.span {c} : Set R)) :=
  idealSheaf_factorization_comap_regular_affine J K _
    (locallyPrincipal_noetherianIdealSheafColon_factorization J K hlocal hdiv) R j A c hJ hK hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalColonFactorization.Construction
