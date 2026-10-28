import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Components

/-! # Right Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RightDifferential

noncomputable section

/-! The three differential components in the bracketing that first
totals the inner two degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]

local instance total (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance complexTotal (K : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

variable (T : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))
open OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Components

theorem right_d (r i j N : ℕ) (hN : r + i + j = N) :
    Components.rightInjection T r i j N hN ≫ (Components.right T).d N (N + 1) =
      ((T.d r (r + 1)).f i).f j ≫ Components.rightInjection T (r + 1) i j (N + 1) (by omega) +
      ((-1 : ℤˣ)^r) •
        (((T.X r).d i (i + 1)).f j ≫ Components.rightInjection T r (i + 1) j (N + 1) (by omega)) +
      ((-1 : ℤˣ)^(r + i)) •
        (((T.X r).X i).d j (j + 1) ≫ Components.rightInjection T r i (j + 1) (N + 1) (by omega)) := by
  have hN' : r + (i + j) = N := by omega
  cases hN'
  rw [Components.rightInjection_eq T (r + 1) i j (i + j) (r + (i + j) + 1) rfl (by omega),
    Components.rightInjection_eq T r (i + 1) j (i + j + 1) (r + (i + j) + 1) (by omega) (by omega),
    Components.rightInjection_eq T r i (j + 1) (i + j + 1) (r + (i + j) + 1) (by omega) (by omega)]
  change (HomologicalComplex₂.ιTotal (T.X r) (.up ℕ) i j (i + j) rfl ≫
    (Components.rightBicomplex T).ιTotal (.up ℕ) r (i + j) (r + (i + j)) rfl) ≫ _ = _
  erw [Category.assoc, AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat, comp_add, Linear.comp_units_smul]
  change (HomologicalComplex₂.ιTotal (T.X r) (.up ℕ) i j (i + j) rfl ≫
    (HomologicalComplex₂.total.map (T.d r (r + 1)) (.up ℕ)).f (i + j) ≫ _) + _ = _
  erw [← Category.assoc, HomologicalComplex₂.ιTotal_map]
  erw [← Category.assoc, AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat]
  erw [add_comp, Linear.units_smul_comp, smul_add, smul_smul, ← pow_add,
    Category.assoc, Category.assoc, Category.assoc]
  symm
  exact add_assoc _ _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RightDifferential
