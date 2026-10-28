import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Local
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.VectorCoefficient
import OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDimensionBound

/-! # Serre Class Formula -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Local

/-! Constructed diagonal section equations give the genuine local
cycle-class formula with the original Serre-Tor intersection coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Local.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.VectorCoefficient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n p q : ℕ) (hn : V.complexDimension = n + 1)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) (Z : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))

local notation "T" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.productVariety V V
local notation "D" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z
local notation "x" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.genericPoint (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z)

include hn in
theorem exists_diagonal_serre_local_class
    (hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier))
    (hproper : ∀ C : IrreducibleCloseds V.carrier,
      (C : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V C) :
    ∃ U : (T).carrier.Opens, ∃ hxU : x ∈ U, letI : Nonempty U := ⟨⟨x, hxU⟩⟩
      ∃ s : Fin (n + 1) → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase U).left, ⊤),
        ProjectiveDiagonalEquations.Constructions.IsDiagonalEquationVector V x (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z) U hxU (n + 1) s ∧
        ∃ W : (T).carrier.Opens, W ≤ U ∧ x ∈ W ∧
          VectorLocalFormula.Constructions.HasLocalVectorFormula T U (p + q) (n + 1) ((p + q) + V.complexDimension) (by omega) s
            (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1)
            (Finsupp.single D (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val)) W := by
  have hdim : V.complexDimension ≤ V.presentation.ambientDimension := by
    simpa only [Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_transcendenceDimension] using
      ProjectiveDimensionBound.integral_dimension_le V
  obtain ⟨U, hxU, s, hs, W, hWU, hxW, hformula⟩ := Local.Constructions.Class.exists_diagonal_local_class V n p q hn A B Z hxA hxB hproper
    V.presentation.ambientDimension (by omega)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [VectorCoefficient.Constructions.diagonal_vector_coefficient V p q A B Z hxA hxB (Section.StalkMap.Constructions.VectorGerms.vectorGerms T U x hxU (n + 1) s) hs.2.2] at hformula
  exact ⟨U, hxU, s, hs, W, hWU, hxW, hformula⟩

end AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Local

namespace AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Equation

/-! The local Serre formula retains any specified actual regular
diagonal section vector, so its analytic coordinate properties remain
available in the Thom comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEquations.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.VectorCoefficient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n p q : ℕ) (hn : V.complexDimension = n + 1)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) (Z : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))

local notation "T" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.productVariety V V
local notation "D" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z
local notation "x" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.genericPoint (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z)

include hn in
theorem exists_serre_formula_for_equations
    (hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier))
    (hproper : ∀ C : IrreducibleCloseds V.carrier,
      (C : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V C)
    (U : (T).carrier.Opens) (hxU : x ∈ U) [Nonempty U]
    (s : Fin (n + 1) → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase U).left, ⊤))
    (hs : ProjectiveDiagonalEquations.Constructions.IsDiagonalEquationVector V x (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z) U hxU (n + 1) s) :
    ∃ W : (T).carrier.Opens, W ≤ U ∧ x ∈ W ∧
      VectorLocalFormula.Constructions.HasLocalVectorFormula T U (p + q) (n + 1) ((p + q) + V.complexDimension) (by omega) s
        (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1)
        (Finsupp.single D (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val)) W := by
  classical
  have hdim : V.complexDimension ≤ V.presentation.ambientDimension := by
    simpa only [Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_transcendenceDimension] using
      ProjectiveDimensionBound.integral_dimension_le V
  have hi := LocalIsolation.Constructions.diagonal_equations_isolated V p q A B Z hxA hxB hproper
    (Section.StalkMap.Constructions.VectorGerms.vectorGerms T U x hxU (n + 1) s) hs.2.2
  obtain ⟨W, hWU, hxW, hformula⟩ := IsolatedVector.Constructions.ClassGeneral.exists_local_vector_formula
    T ((p + q) + V.complexDimension) D n (p + q) (by omega)
    (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1) U hxU s hs.1 hs.2.1
    (by
      intro C hC hxC
      have hEq : C = LocalIsolation.Constructions.pairedSupport V p q A B := by
        by_contra hne
        exact hC (Finsupp.single_eq_of_ne hne)
      subst C
      exact hi) V.presentation.ambientDimension (by omega)
  have hcoeff := VectorCoefficient.Constructions.diagonal_vector_coefficient V p q A B Z hxA hxB (Section.StalkMap.Constructions.VectorGerms.vectorGerms T U x hxU (n + 1) s) hs.2.2
  refine ⟨W, hWU, hxW, ?_⟩
  exact (congrArg (fun r : ℚ => VectorLocalFormula.Constructions.HasLocalVectorFormula T U (p + q) (n + 1)
    ((p + q) + V.complexDimension) (by omega) s (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1)
      (Finsupp.single D r) W) hcoeff).mp hformula

end AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Equation

namespace AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Dimension

/-! The local Serre formula with the actual ambient dimension as its
section-vector length, preserving the specified diagonal equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEquations.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Equation OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) (Z : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))

local notation "T" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.productVariety V V
local notation "D" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z
local notation "x" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.genericPoint (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z)

theorem exists_serre_formula_length
    (r : ℕ) (hr : r = V.complexDimension) (hpos : 0 < r)
    (hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier))
    (hproper : ∀ C : IrreducibleCloseds V.carrier,
      (C : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V C)
    (U : (T).carrier.Opens) (hxU : x ∈ U) [Nonempty U]
    (s : Fin r → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase U).left, ⊤))
    (hs : ProjectiveDiagonalEquations.Constructions.IsDiagonalEquationVector V x (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z) U hxU r s) :
    ∃ W : (T).carrier.Opens, W ≤ U ∧ x ∈ W ∧
      VectorLocalFormula.Constructions.HasLocalVectorFormula T U (p + q) r ((p + q) + V.complexDimension) (by omega) s
        (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1)
        (Finsupp.single D (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val)) W := by
  cases r with
  | zero => omega
  | succ n =>
    exact Equation.exists_serre_formula_for_equations V n p q hr.symm A B Z hxA hxB hproper U hxU s hs

theorem exists_serre_formula_dimension
    (hpos : 0 < V.complexDimension)
    (hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier))
    (hproper : ∀ C : IrreducibleCloseds V.carrier,
      (C : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V C)
    (U : (T).carrier.Opens) (hxU : x ∈ U) [Nonempty U]
    (s : Fin V.complexDimension → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase U).left, ⊤))
    (hs : ProjectiveDiagonalEquations.Constructions.IsDiagonalEquationVector V x (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z) U hxU V.complexDimension s) :
    ∃ W : (T).carrier.Opens, W ≤ U ∧ x ∈ W ∧
      VectorLocalFormula.Constructions.HasLocalVectorFormula T U (p + q) V.complexDimension ((p + q) + V.complexDimension) rfl s
        (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1)
        (Finsupp.single D (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val)) W :=
  exists_serre_formula_length V p q A B Z V.complexDimension rfl hpos hxA hxB hproper U hxU s hs

end AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Dimension

namespace AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Chart

/-! The local Serre formula on a specified genuine etale chart uses
the exact coordinate differences retained by the analytic comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEquations.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Dimension OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) (Z : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))
  (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver) [IsAffine X.left] [IsIntegral X.left] [IsOpenImmersion j.left]
  [Algebra (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  [Algebra.IsStandardEtale (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]

local instance : Nonempty (OpenEquations.Constructions.productOpen V X j) :=
  ⟨⟨OpenEquations.Constructions.center V X j (genericPoint X.left), OpenEquations.Constructions.center_mem V X j (genericPoint X.left)⟩⟩

theorem exists_chart_serre_formula (hpos : 0 < V.complexDimension)
    (hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier))
    (hproper : ∀ C : IrreducibleCloseds V.carrier,
      (C : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V C)
    (y : X.left) (hy : j.left y = Z.genericPoint) :
    ∃ W : (Ambient.Constructions.productVariety V V).carrier.Opens, W ≤ OpenEquations.Constructions.productOpen V X j ∧
      (Ambient.Constructions.diagonalSupport V (p + q) Z).genericPoint ∈ W ∧
      VectorLocalFormula.Constructions.HasLocalVectorFormula (Ambient.Constructions.productVariety V V) (OpenEquations.Constructions.productOpen V X j) (p + q) V.complexDimension
        ((p + q) + V.complexDimension) rfl (OpenEquations.Constructions.diagonalSection V X j V.complexDimension)
        (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1)
        (Finsupp.single (Ambient.Constructions.diagonalSupport V (p + q) Z) (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val)) W := by
  let P := MvPolynomial (Fin V.complexDimension) ℂ
  let : IsNoetherianRing Γ(X.left, ⊤) := Algebra.FiniteType.isNoetherianRing P Γ(X.left, ⊤)
  let : IsNoetherianRing (Γ(X.left, ⊤) ⊗[P] Γ(X.left, ⊤)) := Algebra.FiniteType.isNoetherianRing Γ(X.left, ⊤) _
  have he : OpenEquations.Constructions.center V X j y = (Ambient.Constructions.diagonalSupport V (p + q) Z).genericPoint :=
    (OpenNeighborhood.Constructions.diagonal_point V X j y).trans ((congrArg (Ambient.Constructions.diagonal V).left hy).trans
      (Ambient.Constructions.diagonalSupport_genericPoint V (p + q) Z).symm)
  have hm : (Ambient.Constructions.diagonalSupport V (p + q) Z).genericPoint ∈ OpenEquations.Constructions.productOpen V X j := he ▸ OpenEquations.Constructions.center_mem V X j y
  have hs : ProjectiveDiagonalEquations.Constructions.IsDiagonalEquationVector V (OpenEquations.Constructions.center V X j y) (OpenNeighborhood.Constructions.diagonal_mem V X j y)
      (OpenEquations.Constructions.productOpen V X j) (OpenEquations.Constructions.center_mem V X j y) V.complexDimension (OpenEquations.Constructions.diagonalSection V X j V.complexDimension) :=
    ⟨OpenEquations.Constructions.diagonalGerms_regular V X j V.complexDimension y, OpenEquations.Constructions.diagonalGerms_maximal V X j V.complexDimension y,
      OpenEquations.Constructions.diagonalGerms_ideal V X j V.complexDimension y⟩
  have hs' : ProjectiveDiagonalEquations.Constructions.IsDiagonalEquationVector V (Ambient.Constructions.diagonalSupport V (p + q) Z).genericPoint
      (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z) (OpenEquations.Constructions.productOpen V X j) hm V.complexDimension
      (OpenEquations.Constructions.diagonalSection V X j V.complexDimension) := by
    simpa only [he] using hs
  exact Dimension.exists_serre_formula_dimension V p q A B Z hpos hxA hxB hproper (OpenEquations.Constructions.productOpen V X j) hm
    (OpenEquations.Constructions.diagonalSection V X j V.complexDimension) hs'

end AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Chart

end

end OAI
