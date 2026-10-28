import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Etale
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Group
import Mathlib.CategoryTheory.IsomorphismClasses

/-! # Quotient Graphs -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientGraphs

noncomputable section

/-!
Native scheme kernels and their quotient targets for NeighborCounting. Quotients are
FrobeniusKernel's actual fppf coequalizers, retaining nonreduced subgroup schemes.
The graph-specialization theorem proves its quotient comparison from
Frobenius and base change; no equality of reduced targets is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange.Construction

attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

/-- Actual fppf quotient targets, identified up to isomorphism. -/
abbrev QuotientTarget (S : Scheme.{u}) := Quotient (isIsomorphicSetoid (AbelianScheme.FrobeniusKernel.BaseChange.Construction.FppfSheaves S))

def quotientTarget {S : Scheme.{u}} {A H : Over S} [GrpObj A]
    (i : H ⟶ A) : QuotientTarget S := Quotient.mk _ (AbelianScheme.FrobeniusKernel.BaseChange.Construction.subgroupQuotient i)

def reducedQuotientTarget {S T : Scheme.{u}} (f : T ⟶ S)
    {A H : Over S} [GrpObj A] (i : H ⟶ A) : QuotientTarget T :=
  Quotient.mk _ ((AbelianScheme.FrobeniusKernel.BaseChange.Construction.fppfBaseChange f).obj (AbelianScheme.FrobeniusKernel.BaseChange.Construction.subgroupQuotient i))

/-- Specializing a constructed quotient agrees with quotienting by its
actual specialized kernel. The isomorphism is supplied by base change. -/
theorem reducedQuotientTarget_eq {S T : Scheme.{u}} (f : T ⟶ S)
    {A H : Over S} [GrpObj A] (i : H ⟶ A) :
    reducedQuotientTarget f i = quotientTarget ((Over.pullback f).map i) :=
  Quotient.sound ⟨AbelianScheme.FrobeniusKernel.BaseChange.Construction.subgroupQuotientBaseChangeIso f i⟩

/-- An etale source has no nontrivial maps to a Frobenius-killed group
over a perfect base. This statement concerns actual scheme morphisms. -/
theorem etale_to_frobenius_killed
    {S : Scheme.{u}} (q : ℕ) (hq : q.Prime)
    (hS : (q : Γ(S, ⊤)) = 0)
    [IsIso (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq S hS)]
    {H M : Over S} [GrpObj M] [Etale H.hom]
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS M = 1)
    (χ : H ⟶ M) : χ = 1 := by
  let F := Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq S hS)
  have hleft : IsIso (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS H).left :=
    Picard.Homomorphisms.Etale.Construction.relativeFrobenius_isIso_of_etale q hq hS H
  have : IsIso ((Over.forget S).map (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS H)) := hleft
  have : IsIso (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS H) :=
    isIso_of_reflects_iso _ (Over.forget S)
  apply F.map_injective
  apply (cancel_epi (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS H)).mp
  have hnat := (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat q hq hS).naturality χ
  change χ ≫ Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS M =
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS H ≫ F.map χ at hnat
  rw [hM, MonObj.comp_one] at hnat
  calc
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS H ≫ F.map χ = 1 := hnat.symm
    _ = Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS H ≫ F.map (1 : H ⟶ M) := by
      rw [F.map_one]
      exact (MonObj.comp_one _).symm

/-- Graph kernel in an actual split block of the ambient group scheme. -/
def graphKernel {S : Scheme.{u}} {A M E H : Over S}
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) (χ : H ⟶ M) : H ⟶ A :=
  lift χ e ≫ b

/-- The combined multiplicative and etale kernel uses the product scheme. -/
def mixedKernel {S : Scheme.{u}} {A M E H : Over S}
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) : M ⊗ H ⟶ A :=
  (𝟙 M ⊗ₘ e) ≫ b

theorem graphKernel_specialization {S T : Scheme.{u}} (f : T ⟶ S)
    {A M E H : Over S} [GrpObj M]
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) (χ : H ⟶ M)
    (hχ : (Over.pullback f).map χ = 1) :
    (Over.pullback f).map (graphKernel b e χ) =
      (Over.pullback f).map (graphKernel b e 1) := by
  let F := Over.pullback f
  change F.map (lift χ e ≫ b) = F.map (lift 1 e ≫ b)
  rw [F.map_comp, F.map_comp,
    ← Functor.Monoidal.lift_μ F χ e, ← Functor.Monoidal.lift_μ F 1 e,
    hχ, F.map_one]

/-- All graph parameters have the same specialized kernel. Triviality
of their special characters is derived, not imposed as a target identity. -/
theorem graphKernel_specialization_of_etale
    {S T : Scheme.{u}} (f : T ⟶ S) (q : ℕ) (hq : q.Prime)
    (hT : (q : Γ(T, ⊤)) = 0)
    [IsIso (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq T hT)]
    {A M E H : Over S} [GrpObj M]
    [Etale ((Over.pullback f).obj H).hom]
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hT ((Over.pullback f).obj M) = 1)
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) (χ : H ⟶ M) :
    (Over.pullback f).map (graphKernel b e χ) =
      (Over.pullback f).map (graphKernel b e 1) :=
  graphKernel_specialization f b e χ
    (etale_to_frobenius_killed q hq hT hM ((Over.pullback f).map χ))

theorem reduced_graph_quotient_eq
    {S T : Scheme.{u}} (f : T ⟶ S) (q : ℕ) (hq : q.Prime)
    (hT : (q : Γ(T, ⊤)) = 0)
    [IsIso (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq T hT)]
    {A M E H : Over S} [GrpObj A] [GrpObj M]
    [Etale ((Over.pullback f).obj H).hom]
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hT ((Over.pullback f).obj M) = 1)
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) (χ : H ⟶ M) :
    reducedQuotientTarget f (graphKernel b e χ) =
      quotientTarget ((Over.pullback f).map (graphKernel b e 1)) := by
  rw [reducedQuotientTarget_eq,
    graphKernel_specialization_of_etale f q hq hT hM b e χ]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientGraphs
