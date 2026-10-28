import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ActionsFinite
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ModuliActionsFinite

/-! # Finite Order -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FiniteOrder.Construction

noncomputable section

/-! CentralAction: finite order of the actual central actions on the entire
moduli scheme, the full product Albanese, and full rational H1. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem central_hecke_actions_finite_order
    {E K : Type}
    [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K]
    (s : ℕ) (hdegree : Module.finrank ℚ E = 2 * s)
    (q : ℕ) [Fact q.Prime]
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (active : Fin s) (fullSide : Fin s → Bool)
    (A : Interface.Construction.ActionData D) (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)
    (hFiniteness : Arithmetic.Construction.PrincipalizationInput E) :
    ∃ (σT σC : Aut D.space),
      Interface.Construction.CorrespondenceIsGraph (D.correspondence (CentralRepresentatives.Construction.clearedT3Type active)) (σT ≪≫ A.markingShift) ∧
      Interface.Construction.CorrespondenceIsGraph (D.correspondence (CentralRepresentatives.Construction.c0IntegralType active fullSide)) σC ∧
      ∃ n : ℕ, 0 < n ∧ σT ^ n = 1 ∧ σC ^ n = 1 ∧
        (A.rho (CentralRepresentatives.Construction.T3 s q active)) ^ n = 1 ∧
        (A.rho (CentralRepresentatives.Construction.C0 s q active fullSide)) ^ n = 1 ∧
        (A.rhoH1 (CentralRepresentatives.Construction.T3 s q active)) ^ n = 1 ∧
        (A.rhoH1 (CentralRepresentatives.Construction.C0 s q active fullSide)) ^ n = 1 := by
  obtain ⟨σT, σC, hgT, hgC, hT, hC⟩ := ModuliActionsFinite.Construction.exists_finite_central_moduli_automorphisms
    D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness active fullSide
  have hAT := ActionsFinite.Construction.rho_T3_isOfFinOrder D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness active
  have hAC := ActionsFinite.Construction.rho_C0_isOfFinOrder D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness active fullSide
  obtain ⟨n, hn, hTn, hCn, hATn, hACn⟩ := FiniteOrderAlgebra.Construction.four_finite_common_power
    σT σC (A.rho (CentralRepresentatives.Construction.T3 s q active)) (A.rho (CentralRepresentatives.Construction.C0 s q active fullSide)) hT hC hAT hAC
  exact ⟨σT, σC, hgT, hgC, n, hn, hTn, hCn, hATn, hACn,
    Interface.Construction.h1_power_identity_of_albanese D hgeometry hgood hIsogenyQuotient A hTateComparison (CentralRepresentatives.Construction.T3 s q active) n hATn,
    Interface.Construction.h1_power_identity_of_albanese D hgeometry hgood hIsogenyQuotient A hTateComparison (CentralRepresentatives.Construction.C0 s q active fullSide) n hACn⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FiniteOrder.Construction
