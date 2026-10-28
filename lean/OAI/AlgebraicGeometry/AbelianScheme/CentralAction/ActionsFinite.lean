import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseFinite
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FiniteOrderAlgebra

/-! # Actions Finite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ActionsFinite.Construction

noncomputable section

/-! The actual raw T3 and C0 actions have finite order on the full
product Albanese. The q-scalar clearing factor is itself proved finite. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
  (hgood : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
  (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)
  (hdegree : Module.finrank ℚ E = 2 * s) (hFiniteness : Arithmetic.Construction.PrincipalizationInput E)

include hTateComparison hdegree hFiniteness

theorem rho_integral_central_isOfFinOrder
    (a : Fin s → ℤ) (h : ℤ) (hh : 0 ≤ h) (ha : ∀ v, 0 ≤ a v ∧ a v ≤ h) :
    IsOfFinOrder (A.rho (CentralRepresentatives.Construction.centralCoset s q a h)) := by
  let aN := fun v => (a v).toNat
  let hN := h.toNat
  have hab : ∀ v, aN v ≤ hN := fun v => Int.toNat_le_toNat (ha v).2
  have hcast : (fun v => (aN v : ℤ)) = a := funext (fun v => Int.toNat_of_nonneg (ha v).1)
  have hhcast : (hN : ℤ) = h := Int.toNat_of_nonneg hh
  have hf := AlbaneseFinite.Construction.rho_natCentral_isOfFinOrder D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness aN hN hab
  simpa only [hcast, hhcast] using hf

theorem rho_T3_isOfFinOrder (active : Fin s) : IsOfFinOrder (A.rho (CentralRepresentatives.Construction.T3 s q active)) := by
  have hs := AlbaneseFinite.Construction.rho_natCentral_isOfFinOrder D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness
    (fun _ => 1) 2 (by intro; omega)
  have hc := rho_integral_central_isOfFinOrder D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness
    (fun v => CentralRepresentatives.Construction.t3Exponents active v + 1) 2 (by omega) (by
      intro v
      simp only [CentralRepresentatives.Construction.t3Exponents]
      split_ifs <;> omega)
  have hprod : IsOfFinOrder (A.rho (CentralRepresentatives.Construction.T3 s q active) *
      A.rho (CentralRepresentatives.Construction.centralCoset s q (fun _ => 1) 2)) := by
    rw [← map_mul, CentralRepresentatives.Construction.clearedT3_coset]
    exact hc
  apply FiniteOrderAlgebra.Construction.finite_order_left_of_commuting_product _ hprod hs
  exact (FiniteOrderAlgebra.Construction.centralCoset_commute s q (CentralRepresentatives.Construction.t3Exponents active) (fun _ => 1) 0 2).map A.rho

theorem rho_C0_isOfFinOrder (active : Fin s) (fullSide : Fin s → Bool) :
    IsOfFinOrder (A.rho (CentralRepresentatives.Construction.C0 s q active fullSide)) := by
  apply rho_integral_central_isOfFinOrder D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness
    (CentralRepresentatives.Construction.c0Exponents active fullSide) 1 (by omega)
  intro v
  simp only [CentralRepresentatives.Construction.c0Exponents]
  split_ifs <;> omega

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ActionsFinite.Construction
