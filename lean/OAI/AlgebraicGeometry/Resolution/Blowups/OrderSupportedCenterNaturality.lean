import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedOpenIdealUniqueness
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback

/-! # Order Supported Center Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.OrderSupportedCenterNaturality.Construction

noncomputable section

/-! Equality of permissible centers on an order neighborhood determines their exact global étale pullback equality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem permissible_center_eq_of_order_neighborhood
    {V X : Scheme} [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J I K : X.IdealSheafData) (b : ℕ) (hb : 0 < b) (hI : J ≤ I ^ b) (hK : J ≤ K ^ b)
    (j : V ⟶ X) [IsOpenImmersion j]
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range j)
    (hlocal : I.comap j = K.comap j) : I = K := by
  have hn : b - 1 + 1 = b := Nat.sub_add_cancel hb
  have hTI := Global.OrderLocusPreservation.Construction.global_tangent_le_permissible_center f J I (b - 1) (hn.symm ▸ hI)
  have hTK := Global.OrderLocusPreservation.Construction.global_tangent_le_permissible_center f J K (b - 1) (hn.symm ▸ hK)
  exact SupportedOpenIdealUniqueness.Construction.idealSheaf_eq_of_supported_open j I K
    (fun _ hx => hcover (Scheme.IdealSheafData.support_antitone hTI hx))
    (fun _ hx => hcover (Scheme.IdealSheafData.support_antitone hTK hx)) hlocal

theorem permissible_center_comap_eq_of_order_neighborhood
    {X Y U : Scheme} [IsLocallyNoetherian Y] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (q : Y ⟶ X) [Etale q] (J I : X.IdealSheafData) (K : Y.IdealSheafData)
    (b : ℕ) (hb : 0 < b) (hI : J ≤ I ^ b) (hK : J.comap q ≤ K ^ b)
    (j : U ⟶ Y) [IsOpenImmersion j]
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (q ≫ f) (J.comap q) (b - 1)).support : Set Y) ⊆ Set.range j)
    (hlocal : (I.comap q).comap j = K.comap j) : I.comap q = K := by
  have hI' : J.comap q ≤ (I.comap q) ^ b := by
    rw [← IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow]
    exact Scheme.IdealSheafData.comap_mono q hI
  exact permissible_center_eq_of_order_neighborhood (q ≫ f) (J.comap q) (I.comap q) K b hb hI' hK j hcover hlocal

end

end OAI.AlgebraicGeometry.Resolution.Blowups.OrderSupportedCenterNaturality.Construction
