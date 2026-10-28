import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.ChartDeRham

/-! # Chart Divided Powers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.ChartDividedPowers

noncomputable section

/-! A genuine standard étale chart over a finite Witt level carries
the canonical divided powers on its principal special-fiber ideal. -/

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (σ : Type u) [Finite σ] (A : Type u) [CommRing A]
  [Algebra (Witt.Ring p k n) A]
  [Algebra (MvPolynomial σ (Witt.Ring p k n)) A]
  [IsScalarTower (Witt.Ring p k n)
    (MvPolynomial σ (Witt.Ring p k n)) A]
  (P : StandardEtalePresentation (MvPolynomial σ (Witt.Ring p k n)) A)

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.StandardEtaleLift.Ring p k n σ A P
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.Ring p L n
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.ideal p L n
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.dividedPowers p k L n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.StandardEtaleLift.quotientEquiv p k n σ A P

omit [Fintype k] [CharP k p] [Finite σ] [Algebra S A] [IsScalarTower S (MvPolynomial σ S) A] in
private theorem ideal_map : (I).map (e).toRingHom = Ideal.span {(p : A)} := by
  rw [SmoothWitt.FrameRing.ideal, AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.ideal, Ideal.map_map,
    Ideal.map_span, Set.image_singleton, map_natCast]

def dividedPowers : DividedPowers (Ideal.span {(p : A)}) :=
  DividedPowers.ofRingEquiv (ideal_map p k n σ A P) δ

omit [Fintype k] [Algebra S A] [IsScalarTower S (MvPolynomial σ S) A] in
theorem quotient_isDPMorphism :
    DividedPowers.IsDPMorphism δ (dividedPowers p k n σ A P) (e).toRingHom := by
  refine ⟨(ideal_map p k n σ A P).le, ?_⟩
  intro m a ha
  exact DividedPowers.ofRingEquiv_dpow_apply (ideal_map p k n σ A P) δ

omit [Fintype k] in
theorem wittBase_isDPMorphism :
    DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (dividedPowers p k n σ A P) ((algebraMap S A).comp (Witt.quotient p k n)) := by
  have he : (e).toRingHom.comp (SmoothWitt.FrameRing.base p k L n) =
      (algebraMap S A).comp (Witt.quotient p k n) := by
    ext w
    exact (StandardEtaleLift.quotientEquiv_mk p k n σ A P (algebraMap W L w)).trans
      (StandardEtaleLift.reduction_base p k n σ A P w)
  rw [← he]
  exact (quotient_isDPMorphism p k n σ A P).comp _
    (SmoothWitt.FrameRing.base_isDPMorphism p k L n)

omit [Fintype k] in
theorem base_isDPMorphism :
    DividedPowers.IsDPMorphism (Witt.dividedPowers p k n)
      (dividedPowers p k n σ A P) (algebraMap S A) :=
  DividedPowers.IsDPMorphism.of_comp (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.dividedPowers p k n) (dividedPowers p k n σ A P)
    (Witt.quotient p k n) (algebraMap S A) rfl
    (Witt.quotient_isDPMorphism p k n) (wittBase_isDPMorphism p k n σ A P)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.ChartDividedPowers
