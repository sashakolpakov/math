import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleProjectiveNeighborhood

/-! # Projective Diagonal Equations -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEquations.Constructions

noncomputable section

/-! The original geometric diagonal has actual local regular section
equations of length equal to the variety's complex dimension at every
scheme point. No local-equation hypothesis is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleProjectiveNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def IsDiagonalEquationVector (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x : (Diagonal.Ambient.Constructions.productVariety V V).carrier)
    (hx : x ∈ (Diagonal.Support.Constructions.diagonalClosedSupport V : Set (Diagonal.Ambient.Constructions.productVariety V V).carrier))
    (B : (Diagonal.Ambient.Constructions.productVariety V V).carrier.Opens) (hxB : x ∈ B)
    (n : ℕ) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) : Prop :=
  IsWeaklyRegular ((Diagonal.Ambient.Constructions.productVariety V V).carrier.presheaf.stalk x)
    (Section.StalkMap.Constructions.VectorGerms.vectorGerms (Diagonal.Ambient.Constructions.productVariety V V) B x hxB n s) ∧
  (∀ a ∈ Section.StalkMap.Constructions.VectorGerms.vectorGerms (Diagonal.Ambient.Constructions.productVariety V V) B x hxB n s,
    a ∈ IsLocalRing.maximalIdeal ((Diagonal.Ambient.Constructions.productVariety V V).carrier.presheaf.stalk x)) ∧
  Ideal.ofList (Section.StalkMap.Constructions.VectorGerms.vectorGerms (Diagonal.Ambient.Constructions.productVariety V V) B x hxB n s) =
    (StalkPrimeQuotient.Constructions.kernelPrime (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.Support.Constructions.diagonalClosedSupport V) x hx).asIdeal

theorem point_mem_diagonal (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x : V.carrier) :
    (Diagonal.Ambient.Constructions.diagonal V).left x ∈ (Diagonal.Support.Constructions.diagonalClosedSupport V : Set (Diagonal.Ambient.Constructions.productVariety V V).carrier) := by
  rw [Diagonal.Support.Constructions.diagonalClosedSupport_coe]
  exact ⟨x, rfl⟩

theorem exists_diagonal_equations (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x : V.carrier) :
    ∃ B : (Diagonal.Ambient.Constructions.productVariety V V).carrier.Opens, ∃ hxB : (Diagonal.Ambient.Constructions.diagonal V).left x ∈ B,
      ∃ s : Fin V.complexDimension → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤),
        IsDiagonalEquationVector V ((Diagonal.Ambient.Constructions.diagonal V).left x) (point_mem_diagonal V x)
          B hxB V.complexDimension s := by
  obtain ⟨X, hX, j, hj, hI, hS, ⟨y, hy⟩, a, ht, he⟩ := EtaleProjectiveNeighborhood.Constructions.exists_etale_projective_neighborhood V x
  let := hX
  let := hj
  let := hI
  let := hS
  let := a
  let := ht
  let := he
  let P := MvPolynomial (Fin V.complexDimension) ℂ
  let : IsNoetherianRing Γ(X.left, ⊤) := Algebra.FiniteType.isNoetherianRing P Γ(X.left, ⊤)
  let : IsNoetherianRing (Γ(X.left, ⊤) ⊗[P] Γ(X.left, ⊤)) :=
    Algebra.FiniteType.isNoetherianRing Γ(X.left, ⊤) _
  have hc : Diagonal.OpenEquations.Constructions.center V X j y = (Diagonal.Ambient.Constructions.diagonal V).left x :=
    (Diagonal.OpenNeighborhood.Constructions.diagonal_point V X j y).trans (congrArg (Diagonal.Ambient.Constructions.diagonal V).left hy)
  have h : ∃ B : (Diagonal.Ambient.Constructions.productVariety V V).carrier.Opens, ∃ hxB : Diagonal.OpenEquations.Constructions.center V X j y ∈ B,
      ∃ s : Fin V.complexDimension → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤),
        IsDiagonalEquationVector V (Diagonal.OpenEquations.Constructions.center V X j y) (Diagonal.OpenNeighborhood.Constructions.diagonal_mem V X j y)
          B hxB V.complexDimension s := by
    exact ⟨Diagonal.OpenEquations.Constructions.productOpen V X j, Diagonal.OpenEquations.Constructions.center_mem V X j y, Diagonal.OpenEquations.Constructions.diagonalSection V X j V.complexDimension,
      Diagonal.OpenEquations.Constructions.diagonalGerms_regular V X j V.complexDimension y,
      Diagonal.OpenEquations.Constructions.diagonalGerms_maximal V X j V.complexDimension y,
      Diagonal.OpenEquations.Constructions.diagonalGerms_ideal V X j V.complexDimension y⟩
  simpa only [hc] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEquations.Constructions
