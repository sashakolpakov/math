import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Components

/-! # Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Differential

noncomputable section

/-! Both bracketings retain the same three native differential
components, with signs 1, (-1)^r, and (-1)^(r+i). -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]

local instance total (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance complexTotal (K : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

variable (T : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))
open OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Components

omit [HasFiniteCoproducts A] in
theorem left_inner (r i j : ℕ) :
    (T.ιTotal (.up ℕ) r i (r + i) rfl).f j ≫
      ((Components.leftBicomplex T).d (r + i) (r + i + 1)).f j =
    ((T.d r (r + 1)).f i).f j ≫
      (T.ιTotal (.up ℕ) (r + 1) i (r + i + 1) (by change r + 1 + i = r + i + 1; omega)).f j +
    ((-1 : ℤˣ)^r) • (((T.X r).d i (i + 1)).f j ≫
      (T.ιTotal (.up ℕ) r (i + 1) (r + i + 1) (by change r + (i + 1) = r + i + 1; omega)).f j) := by
  have hd := congrArg (HomologicalComplex.eval A (.up ℕ) j).map ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat T) r i)
  simp only [Functor.map_comp, Functor.map_add, Functor.map_units_smul] at hd
  exact hd

theorem left_d (r i j N : ℕ) (hN : r + i + j = N) :
    Components.leftInjection T r i j N hN ≫ (Components.left T).d N (N + 1) =
      ((T.d r (r + 1)).f i).f j ≫ Components.leftInjection T (r + 1) i j (N + 1) (by omega) +
      ((-1 : ℤˣ)^r) •
        (((T.X r).d i (i + 1)).f j ≫ Components.leftInjection T r (i + 1) j (N + 1) (by omega)) +
      ((-1 : ℤˣ)^(r + i)) •
        (((T.X r).X i).d j (j + 1) ≫ Components.leftInjection T r i (j + 1) (N + 1) (by omega)) := by
  subst N
  rw [Components.leftInjection_eq T (r + 1) i (r + i + 1) j (r + i + j + 1) (by omega) (by omega),
    Components.leftInjection_eq T r (i + 1) (r + i + 1) j (r + i + j + 1) (by omega) (by omega),
    Components.leftInjection_eq T r i (r + i) (j + 1) (r + i + j + 1) rfl (by omega)]
  change ((T.ιTotal (.up ℕ) r i (r + i) rfl).f j ≫
    (Components.leftBicomplex T).ιTotal (.up ℕ) (r + i) j (r + i + j) rfl) ≫ _ = _
  erw [Category.assoc, AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat, comp_add, Linear.comp_units_smul,
    ← Category.assoc, left_inner, add_comp, Linear.units_smul_comp]
  have hv := (T.ιTotal (.up ℕ) r i (r + i) rfl).comm j (j + 1)
  erw [← Category.assoc, hv]
  dsimp only [Components.leftBicomplex]
  erw [Category.assoc, Category.assoc, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Differential
