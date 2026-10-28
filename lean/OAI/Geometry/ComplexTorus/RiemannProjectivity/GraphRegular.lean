import OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalizedGraph
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Localization.Submodule
import OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt

/-! # Graph Regular -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.GraphVanishingIdeal

/-! # RiemannProjectivity: the actual vanishing ideal has a smooth neighborhood along a regular graph -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology
open OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SmoothEquationPoint OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphGermsOn.Constructions.GraphGerms OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalizedGraph.Constructions.LocalizedGraphGerms

variable {n m : ℕ}

def polynomialMap (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) :
    MvPolynomial (Fin n ⊕ Fin m) ℂ →+* LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F :=
  (algebraMap (JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F) (LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F)).comp (Ideal.Quotient.mk _)

def vanishingIdeal (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (S : Set (Fin n ⊕ Fin m → ℂ)) : Ideal (LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F) :=
  (MvPolynomial.vanishingIdeal ℂ S).map (polynomialMap F)

theorem branchMap_polynomial (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (ψ x j) ≠ 0)
    (p : MvPolynomial (Fin n ⊕ Fin m) ℂ) :
    LocalizedGraph.Constructions.LocalizedGraphGerms.branchMap F x ψ hU hx hψ hzero hderiv (polynomialMap F p) =
      GraphGermsOn.Constructions.GraphGerms.polynomialMap x ψ hU hx hψ p := by
  change IsLocalization.Away.lift (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian
    (LocalizedGraph.Constructions.LocalizedGraphGerms.jacobian_unit F x ψ hU hx hψ hzero hderiv)
    (algebraMap (JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F) (LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F) (Ideal.Quotient.mk _ p)) = _
  rw [IsLocalization.Away.lift_eq]
  rfl

theorem vanishingIdeal_le_kernel
    (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (ψ x j) ≠ 0)
    (S : Set (Fin n ⊕ Fin m → ℂ)) (hS : ∀ y ∈ U, GraphGermsOn.Constructions.GraphGerms.graph ψ y ∈ S) :
    GraphVanishingIdeal.vanishingIdeal F S ≤ RingHom.ker (LocalizedGraph.Constructions.LocalizedGraphGerms.branchMap F x ψ hU hx hψ hzero hderiv).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro p hp
  change LocalizedGraph.Constructions.LocalizedGraphGerms.branchMap F x ψ hU hx hψ hzero hderiv (polynomialMap F p) = 0
  rw [branchMap_polynomial]
  apply (PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms.pullback_eq_zero x (GraphGermsOn.Constructions.GraphGerms.graph ψ) hU hx
    (GraphGermsOn.Constructions.GraphGerms.differentiableOn_graph ψ hψ) p).mpr
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hp (GraphGermsOn.Constructions.GraphGerms.graph ψ y) (hS y hy)

theorem exists_smooth_neighborhood
    (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) (hF : ∀ j, F j ≠ 0)
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (ψ x j) ≠ 0)
    (S : Set (Fin n ⊕ Fin m → ℂ)) (hS : ∀ y ∈ U, GraphGermsOn.Constructions.GraphGerms.graph ψ y ∈ S) :
    ∃ s : LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F,
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x (LocalizedGraph.Constructions.LocalizedGraphGerms.branchMap F x ψ hU hx hψ hzero hderiv s) ≠ 0 ∧
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (GraphVanishingIdeal.vanishingIdeal F S) s)) := by
  have hfg : (GraphVanishingIdeal.vanishingIdeal F S).FG := IsNoetherian.noetherian _
  exact LocalizedGraph.Constructions.LocalizedGraphGerms.exists_smooth_quotient_neighborhood F hF x ψ hU hx hψ hzero hderiv _ hfg
    (vanishingIdeal_le_kernel F x ψ hU hx hψ hzero hderiv S hS)

theorem exists_smooth_point_neighborhood
    (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) (hF : ∀ j, F j ≠ 0)
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (ψ x j) ≠ 0)
    (S : Set (Fin n ⊕ Fin m → ℂ)) (hS : ∀ y ∈ U, GraphGermsOn.Constructions.GraphGerms.graph ψ y ∈ S) :
    ∃ (s : LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F) (q : LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F →ₐ[ℂ] ℂ),
      (∀ p, q (polynomialMap F p) = MvPolynomial.eval (GraphGermsOn.Constructions.GraphGerms.graph ψ x) p) ∧
      q s ≠ 0 ∧ Algebra.Smooth ℂ
        (Localization.Away (Ideal.Quotient.mk (GraphVanishingIdeal.vanishingIdeal F S) s)) := by
  obtain ⟨s, hs, hsm⟩ := exists_smooth_neighborhood F hF x ψ hU hx hψ hzero hderiv S hS
  refine ⟨s, LocalizedGraph.Constructions.LocalizedGraphGerms.branchPoint F x ψ hU hx hψ hzero hderiv, ?_, hs, hsm⟩
  intro p
  change AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x (LocalizedGraph.Constructions.LocalizedGraphGerms.branchMap F x ψ hU hx hψ hzero hderiv (polynomialMap F p)) = _
  rw [branchMap_polynomial]
  exact PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms.pullback_value x (GraphGermsOn.Constructions.GraphGerms.graph ψ) hU hx
    (GraphGermsOn.Constructions.GraphGerms.differentiableOn_graph ψ hψ) p

end Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.GraphVanishingIdeal

namespace Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.RegularConeNeighborhood

/-! # RiemannProjectivity: smooth algebraic neighborhoods at the actual normalized cone points -/

open Set _root_.Polynomial
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalizedGraph.Constructions.LocalizedGraphGerms

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b : ℕ}

def splitPoint (e : V ≃L[ℂ] ((Fin a → ℂ) × (Fin b → ℂ))) (w : V) :
    Fin a ⊕ Fin b → ℂ := Sum.elim (e w).1 (e w).2

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {n : ℕ}

theorem exists_at_parameter (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (i : Fin (n + 1)) (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)
    (hi : f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv : v.val = ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1)) :
    ∃ (m : ℕ) (e : (Fin (n + 1) → ℂ) ≃L[ℂ]
        ((Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ) × (Fin m → ℂ)))
      (F : Fin m → Polynomial (MvPolynomial (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1)) ℂ))
      (s : LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F) (q : LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F →ₐ[ℂ] ℂ),
      (∀ w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), ∀ j,
        MvPolynomial.eval (splitPoint e w) (JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (F j)) = 0) ∧
      (∀ p, q (GraphVanishingIdeal.polynomialMap F p) = MvPolynomial.eval (splitPoint e v.val) p) ∧
      q s ≠ 0 ∧ Algebra.Smooth ℂ
        (Localization.Away (Ideal.Quotient.mk
          (GraphVanishingIdeal.vanishingIdeal F (splitPoint e '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))) s)) := by
  obtain ⟨L, m, e, F, he, hInv, hF, hder, hzero⟩ :=
    JacobianLocalizationAt.Constructions.RegularConeEquations.exists_at_parameter Φ f hf hd i z hi v hv
  obtain ⟨r, hvr, hr, hdr⟩ := hInv
  have hx : L v ∈ r.target := by
    rw [← congrFun hr v]
    exact r.map_source hvr
  have hinv : r.symm (L v) = v := by
    rw [← congrFun hr v]
    exact r.left_inv hvr
  let ψ := fun y => (e (r.symm y).val).2
  have hψ : DifferentiableOn ℂ ψ r.target :=
    (e.differentiable.comp_differentiableOn hdr).snd
  have hbase (y) (hy : y ∈ r.target) : (e (r.symm y).val).1 = y := by
    rw [he, ← congrFun hr (r.symm y)]
    exact r.right_inv hy
  have hz (y) (hy : y ∈ r.target) (j : Fin m) :
      (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0 := by
    have h := hzero j (r.symm y).val (r.symm y).property
    rw [← he, hbase y hy, SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate_apply] at h
    exact h
  have hdψ (j : Fin m) : ((F j).map (MvPolynomial.eval (L v))).derivative.eval (ψ (L v) j) ≠ 0 := by
    simpa only [ψ, hinv, SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate_apply] using hder j
  have hS (y) (hy : y ∈ r.target) : GraphGermsOn.Constructions.GraphGerms.graph ψ y ∈
      splitPoint e '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
    refine ⟨(r.symm y).val, (r.symm y).property, ?_⟩
    funext j
    cases j with
    | inl j => exact congrFun (hbase y hy) j
    | inr j => rfl
  obtain ⟨s, q, hq, hs, hsm⟩ := GraphVanishingIdeal.exists_smooth_point_neighborhood
    F hF (L v) ψ r.open_target hx hψ hz hdψ _ hS
  refine ⟨m, e, F, s, q, ?_, ?_, hs, hsm⟩
  · intro w hw j
    change MvPolynomial.eval (Sum.elim (e w).1 (e w).2)
      (JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (F j)) = 0
    rw [JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.eval_equation, he]
    exact hzero j w hw
  intro p
  rw [hq]
  have hg : GraphGermsOn.Constructions.GraphGerms.graph ψ (L v) = splitPoint e v.val := by
    funext j
    cases j with
    | inl j => exact congrFun (he v.val).symm j
    | inr j => change (e (r.symm (L v)).val).2 j = (e v.val).2 j; rw [hinv]
  rw [hg]

end Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.RegularConeNeighborhood

end

end OAI
