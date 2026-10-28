import OAI.AlgebraicGeometry.Resolution.Blowups.ReducedGlobalBlowupLift
import OAI.AlgebraicGeometry.Resolution.Blowups.RegularPrincipalDenseComplement
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenBoundaryTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.TransformRegularElements

/-! # Affine Global Blowup Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.AffineGlobalBlowupLift.Construction

noncomputable section

/-! A regular principal center pullback gives an actual global blowup lift from any reduced affine source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affine_regular_kernel_native_generators
    (R : CommRingCat.{0}) (K : (Spec R).IdealSheafData) (c : R) (hc : IsRegular c)
    (hK : K = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {c})) (x : Spec R) :
    ∃ U : (Spec R).affineOpens, x ∈ U.1 ∧
      ∃ r : Γ(Spec R, U), IsRegular r ∧ K.ideal U = Ideal.span {r} := by
  let j : Spec R ⟶ Spec R := 𝟙 _
  let e := Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv R j
  have hmap : K.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {c}) := by
    rw [Scheme.IdealSheafData.comap_id]
    exact hK
  refine ⟨Affine.OpenBoundaryTransport.Construction.specOpenImage R j, ?_, e.symm c, ?_, Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_equation R j K c hmap⟩
  · rw [Affine.OpenBoundaryTransport.Construction.specOpenImage_eq_opensRange]
    exact ⟨x, rfl⟩
  · exact TransformRegularElements.Construction.etale_ringHom_preserves_regular e.symm.toRingHom (RingHom.Etale.of_bijective e.symm.bijective) c hc

theorem existsUnique_globalBlowup_lift_reduced_affine
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat.{0}) [_root_.IsReduced R]
    (q : Spec R ⟶ X) (c : R) (hc : IsRegular c)
    (hIshape : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {c})) :
    ∃! l : Spec R ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI, l ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = q := by
  apply ReducedGlobalBlowupLift.Construction.existsUnique_globalBlowup_lift_of_regular_generators I hI q
  · have hd := RegularPrincipalDenseComplement.Construction.regular_affineQuotientKernel_supportComplement_dense c hc
    rw [← hIshape, Scheme.IdealSheafData.support_comap] at hd
    exact hd
  · exact affine_regular_kernel_native_generators R (I.comap q) c hc hIshape

def reducedAffineGlobalBlowupLift
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat.{0}) [_root_.IsReduced R]
    (q : Spec R ⟶ X) (c : R) (hc : IsRegular c)
    (hIshape : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {c})) : Spec R ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI :=
  (existsUnique_globalBlowup_lift_reduced_affine I hI R q c hc hIshape).choose

theorem reducedAffineGlobalBlowupLift_over
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat.{0}) [_root_.IsReduced R]
    (q : Spec R ⟶ X) (c : R) (hc : IsRegular c)
    (hIshape : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {c})) :
    reducedAffineGlobalBlowupLift I hI R q c hc hIshape ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = q :=
  (existsUnique_globalBlowup_lift_reduced_affine I hI R q c hc hIshape).choose_spec.1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.AffineGlobalBlowupLift.Construction
