import OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleProjectiveNeighborhood

/-! # Geometric Diagonal Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GeometricDiagonalEuler.Constructions

noncomputable section

/-! Genuine geometric reduction to the diagonal for the original
local-support Tor Euler sum. The proof constructs coordinates and
discharges their hypotheses at every scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions.Restriction
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleProjectiveNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.QuotientEulerEquiv.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def supportPairEuler (X : Scheme) (A B : IrreducibleCloseds X) (x : X) (d : ℕ) : ℚ :=
  if h : x ∈ (A : Set X) ∩ (B : Set X) then
    TorAlgebra.Euler.Tor.euler (X.presheaf.stalk x) (IntersectionGeometry.localSupportModule X A x h.1) (IntersectionGeometry.localSupportModule X B x h.2) d
  else 0

theorem supportPairEuler_eq_quotients (X : Scheme) (A B : IrreducibleCloseds X)
    (x : X) (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X)) (d : ℕ) :
    supportPairEuler X A B x d = TorAlgebra.Euler.Tor.euler (X.presheaf.stalk x)
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X A x hxA)) (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X B x hxB)) d := by
  rw [supportPairEuler, dite_eq_left ⟨hxA, hxB⟩]
  exact Open.SupportEuler.Constructions.nativeEuler_eq_quotients X A B x hxA hxB d

theorem supportPairEuler_in_chart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)
    [IsAffine X.left] [IsIntegral X.left] [IsOpenImmersion j.left] [LocallyOfFiniteType X.hom]
    (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
    (x : X.left) (hxA : j.left x ∈ (A.val : Set V.carrier)) (hxB : j.left x ∈ (B.val : Set V.carrier))
    (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [Algebra.FormallyUnramified (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [IsNoetherianRing (Γ(X.left, ⊤) ⊗[MvPolynomial (Fin n) ℂ] Γ(X.left, ⊤))] (d : ℕ) :
    supportPairEuler V.carrier A.val B.val (j.left x) d =
      supportPairEuler (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.Support.Constructions.diagonalClosedSupport V) (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val
        (Diagonal.OpenEquations.Constructions.center V X j x) d := by
  have hA := Open.StalkSupport.Constructions.Restriction.generic_mem_range j.left A.val x hxA
  have hB := Open.StalkSupport.Constructions.Restriction.generic_mem_range j.left B.val x hxB
  have h₁ := supportPairEuler_eq_quotients V.carrier A.val B.val (j.left x) hxA hxB d
  have h₂ := ProjectiveDiagonalEuler.Constructions.projective_diagonal_euler V X j p q A B hA hB x hxA hxB n d
  have h₃ := Local.QuotientEulerEquiv.Constructions.euler_quotients_congr (Diagonal.OpenEquations.Constructions.ambientLocalRing V X j x)
    (Ideal.ofList (Diagonal.OpenEquations.Constructions.diagonalGerms V X j n x))
    (StalkPrimeQuotient.Constructions.kernelPrime (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val
      (Diagonal.OpenEquations.Constructions.center V X j x) (ProjectiveDiagonalEuler.Constructions.pair_center_mem V X j p q A B x hxA hxB)).asIdeal
    (StalkPrimeQuotient.Constructions.kernelPrime (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.Support.Constructions.diagonalClosedSupport V)
      (Diagonal.OpenEquations.Constructions.center V X j x) (Diagonal.OpenNeighborhood.Constructions.diagonal_mem V X j x)).asIdeal
    (StalkPrimeQuotient.Constructions.kernelPrime (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val
      (Diagonal.OpenEquations.Constructions.center V X j x) (ProjectiveDiagonalEuler.Constructions.pair_center_mem V X j p q A B x hxA hxB)).asIdeal
    (Diagonal.OpenEquations.Constructions.diagonalGerms_ideal V X j n x) rfl d
  have h₄ := supportPairEuler_eq_quotients (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.Support.Constructions.diagonalClosedSupport V)
    (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val (Diagonal.OpenEquations.Constructions.center V X j x) (Diagonal.OpenNeighborhood.Constructions.diagonal_mem V X j x)
    (ProjectiveDiagonalEuler.Constructions.pair_center_mem V X j p q A B x hxA hxB) d
  exact h₁.trans (h₂.trans (h₃.trans h₄.symm))

theorem supportPairEuler_diagonal (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
    (x : V.carrier) (hxA : x ∈ (A.val : Set V.carrier)) (hxB : x ∈ (B.val : Set V.carrier)) (d : ℕ) :
    supportPairEuler V.carrier A.val B.val x d =
      supportPairEuler (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.Support.Constructions.diagonalClosedSupport V) (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val
        ((Diagonal.Ambient.Constructions.diagonal V).left x) d := by
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
  let : IsNoetherianRing (Γ(X.left, ⊤) ⊗[P] Γ(X.left, ⊤)) := Algebra.FiniteType.isNoetherianRing Γ(X.left, ⊤) _
  have hya : j.left y ∈ (A.val : Set V.carrier) := hy.symm ▸ hxA
  have hyb : j.left y ∈ (B.val : Set V.carrier) := hy.symm ▸ hxB
  have hc : Diagonal.OpenEquations.Constructions.center V X j y = (Diagonal.Ambient.Constructions.diagonal V).left x :=
    (Diagonal.OpenNeighborhood.Constructions.diagonal_point V X j y).trans (congrArg (Diagonal.Ambient.Constructions.diagonal V).left hy)
  simpa only [hy, hc] using supportPairEuler_in_chart V X j p q A B y hya hyb V.complexDimension d

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GeometricDiagonalEuler.Constructions
