import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.AffineExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.HigherAvoidance
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartSupportCover

/-! # Descent Position -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.DescentPosition

noncomputable section

/-! One representative simultaneously has native numerator and
denominator Euler expansions on every support chart, meets the support
properly, and permits restriction of the rational function to every
generic intersection component. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

def PrimeData (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ) (W : IrreducibleCloseds X.carrier)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (F : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W × Bool, Finset (PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W i.1))) : Prop :=
  ∀ i, ∀ z ∈ F i, (Affine.ChartGerm.FiniteSupportCharts.prime X W i.1).asIdeal ≤ z.asIdeal ∧
    ChartEquations.equation X W g hg i ∈ z.asIdeal ∧
    X.supportCodimension (Affine.FiltrationAvoidance.support (R := Affine.ChartGerm.FiniteSupportCharts.ring X W i.1)
      (Affine.ChartGerm.FiniteSupportCharts.chart X W i.1) z) = k + 1

def familyExpansion (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ) {τ : Type}
    (R : τ → Type) [∀ i, CommRing (R i)] [∀ i, IsNoetherianRing (R i)]
    (j : ∀ i, Spec (.of (R i)) ⟶ X.carrier) (v : ∀ i, PrimeSpectrum (R i)) (r : ∀ i, R i)
    (F : ∀ i, Finset (PrimeSpectrum (R i))) (a : X.RationalDimensionCycle p) : Prop :=
  ∀ i, AffineExpansion.Expansion X p q (j i) (v i) (r i) (F i) a

def familyOutside (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ) {τ : Type}
    (R : τ → Type) [∀ i, CommRing (R i)] [∀ i, IsNoetherianRing (R i)]
    (j : ∀ i, Spec (.of (R i)) ⟶ X.carrier) (v : ∀ i, PrimeSpectrum (R i)) (r : ∀ i, R i)
    (F : ∀ i, Finset (PrimeSpectrum (R i))) : Prop :=
  ∀ i, ∀ z : PrimeSpectrum (R i), X.supportCodimension (Affine.FiltrationAvoidance.support (j i) z) = q →
    z ∉ F i → Affine.PrincipalWeight.weight (R i) (v i) (r i) z = 0

def Outside (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ) (W : IrreducibleCloseds X.carrier)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (F : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W × Bool, Finset (PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W i.1))) : Prop :=
  familyOutside X (k + 1) (fun i : Affine.ChartGerm.FiniteSupportCharts.Index X W × Bool => (Affine.ChartGerm.FiniteSupportCharts.ring X W i.1 : Type))
    (fun i => Affine.ChartGerm.FiniteSupportCharts.chart X W i.1) (fun i => Affine.ChartGerm.FiniteSupportCharts.prime X W i.1) (ChartEquations.equation X W g hg) F

def Expansions (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p k : ℕ) (W : IrreducibleCloseds X.carrier)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (F : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W × Bool, Finset (PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W i.1)))
    (a : X.RationalDimensionCycle p) : Prop :=
  familyExpansion X p (k + 1) (fun i : Affine.ChartGerm.FiniteSupportCharts.Index X W × Bool => (Affine.ChartGerm.FiniteSupportCharts.ring X W i.1 : Type))
    (fun i => Affine.ChartGerm.FiniteSupportCharts.chart X W i.1) (fun i => Affine.ChartGerm.FiniteSupportCharts.prime X W i.1) (ChartEquations.equation X W g hg) F a

def Units (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p k : ℕ) (W : IrreducibleCloseds X.carrier)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (a : X.RationalDimensionCycle p) : Prop :=
  ∀ A ∈ a.support, ∀ C : X.DimensionCycleSupport (p + k), C.val ≤ A.val → C.val ≤ W →
    ∀ hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W : Set X.carrier),
    ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW),
      IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField u = g

theorem exists_moved (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    {ι : Type} [Finite ι] (Z₀ : ι → IrreducibleCloseds X.carrier) (a : X.RationalDimensionCycle p) :
    ∃ (F : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool, Finset (PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)))
      (a' : X.RationalDimensionCycle p),
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a' ∧
      a' ∈ Proper.SupportCycles.submodule X p Z₀ ∧
      a' ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg) ∧
      (∀ A ∈ a'.support, Supports.ProperCycle.pairMeetsProperly X p k A W) ∧
      PrimeData X k W.val g hg F ∧ Outside X k W.val g hg F ∧
      Expansions X p k W.val g hg F a' ∧ Units X p k W.val g a' := by
  classical
  obtain ⟨T, _, hT⟩ := Support.HigherAvoidance.UnitStrata.exists_data X m k W g hg
  let J := (ι ⊕ ChartSupportCover.Index X m k W g hg) ⊕ Option T
  let Z : J → IrreducibleCloseds X.carrier :=
    Sum.elim (Sum.elim Z₀ (ChartSupportCover.family X m k W g hg))
      (fun o => o.elim W.val Subtype.val)
  let I := Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool
  let R : I → Type := fun i => Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1
  let j : ∀ i, Spec (.of (R i)) ⟶ X.carrier := fun i => Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1
  let v : ∀ i, PrimeSpectrum (R i) := fun i => Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1
  have hv (i : I) : X.supportCodimension (Affine.FiltrationAvoidance.support (j i) (v i)) = k := by
    rw [show Affine.FiltrationAvoidance.support (j i) (v i) = W.val from Affine.ChartGerm.FiniteSupportCharts.prime_support X W.val i.1]
    exact W.property
  obtain ⟨F, a', ha', hproper, hF, hout, he⟩ :=
    AffineExpansion.Simultaneous.exists_moved X m p R j (fun _ => k) v hv
      (ChartEquations.equation X W.val g hg) (ChartEquations.equation_avoid X W.val g hg) Z a
  refine ⟨F, a', ha', ?_, ?_, ?_, hF, hout, he, ?_⟩
  · intro i A hA
    exact hproper (.inl (.inl i)) A hA
  · intro i A hA
    exact hproper (.inl (.inr i)) A hA
  · intro A hA C hC
    have h := hproper (.inr none) A hA C hC
    change p + X.supportCodimension W.val ≤ X.supportCodimension C at h
    rwa [W.property] at h
  · intro A hA
    apply hT p A
    intro B hB
    exact hproper (.inr (some ⟨B, hB⟩)) A hA

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.DescentPosition
