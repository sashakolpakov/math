import OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEquations
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation
import OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedVector

/-! # Local -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Local.Constructions.Class

noncomputable section

/-! At every original proper-intersection component, the actual
product cycle and constructed diagonal equations satisfy the local
class formula with their genuine ambient Tor Euler coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen
open OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n p q : ℕ) (hn : V.complexDimension = n + 1)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) (Z : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))

local notation "T" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.productVariety V V
local notation "D" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z
local notation "x" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.genericPoint (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z)
local notation "c" => Finsupp.single (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B) (1 : ℚ)

include hn in
theorem exists_diagonal_local_class
    (hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier))
    (hproper : ∀ C : IrreducibleCloseds V.carrier,
      (C : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V C)
    (l : ℕ) (hl : n ≤ l) :
    ∃ U : (T).carrier.Opens, ∃ hxU : x ∈ U, letI : Nonempty U := ⟨⟨x, hxU⟩⟩
      ∃ s : Fin (n + 1) → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase U).left, ⊤),
        ProjectiveDiagonalEquations.Constructions.IsDiagonalEquationVector V x (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z) U hxU (n + 1) s ∧
        ∃ W : (T).carrier.Opens, W ≤ U ∧ x ∈ W ∧
          VectorLocalFormula.Constructions.HasLocalVectorFormula T U (p + q) (n + 1) ((p + q) + V.complexDimension) (by omega) s c
            (Finsupp.single D (Local.Euler.Constructions.localCycleEuler T (p + q) x (Section.StalkMap.Constructions.VectorGerms.vectorGerms T U x hxU (n + 1) s) l c)) W := by
  classical
  have he : ∃ U : (T).carrier.Opens, ∃ hxU : x ∈ U,
      ∃ s : Fin (n + 1) → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase U).left, ⊤),
        ProjectiveDiagonalEquations.Constructions.IsDiagonalEquationVector V x (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z) U hxU (n + 1) s := by
    have h := ProjectiveDiagonalEquations.Constructions.exists_diagonal_equations V Z.genericPoint
    rw [hn] at h
    simpa only [Ambient.Constructions.diagonalSupport_genericPoint] using h
  obtain ⟨U, hxU, s, hs⟩ := he
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hi := LocalIsolation.Constructions.diagonal_equations_isolated V p q A B Z hxA hxB hproper
    (Section.StalkMap.Constructions.VectorGerms.vectorGerms T U x hxU (n + 1) s) hs.2.2
  obtain ⟨W, hWU, hxW, hformula⟩ := IsolatedVector.Constructions.ClassGeneral.exists_local_vector_formula
    T ((p + q) + V.complexDimension) D n (p + q) (by omega) c U hxU s hs.1 hs.2.1
    (by
      intro C hC hxC
      have hEq : C = LocalIsolation.Constructions.pairedSupport V p q A B := by
        by_contra hne
        exact hC (Finsupp.single_eq_of_ne hne)
      subst C
      exact hi) l hl
  exact ⟨U, hxU, s, hs, W, hWU, hxW, hformula⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Local.Constructions.Class
