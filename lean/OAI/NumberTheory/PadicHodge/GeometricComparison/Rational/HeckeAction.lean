import OAI.NumberTheory.PadicHodge.GeometricComparison.BettiGroupAction
import Mathlib.Algebra.Algebra.Opposite

/-! # Hecke Action -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The native Hecke presentations give a genuine rational algebra action on Betti cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

def Geometry.AbelianH1Model.rationalBettiAction :
    (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A.variety.scheme)ᵐᵒᵖ →ₐ[ℚ] Module.End ℚ (A.Betti j) :=
  AlgHom.opComm ((AlgHom.liftEquiv ℤ ℚ (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme)
    (Module.End ℚ (A.Betti j))ᵐᵒᵖ)
      (AlgHom.opComm.symm (A.algebraicBettiRingAction j P).toIntAlgHom))

theorem Geometry.AbelianH1Model.rationalBettiAction_tmul (r : ℚ) (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme) :
    A.rationalBettiAction j P (MulOpposite.op (r ⊗ₜ[ℤ] f)) = r • A.algebraicBettiPullback j f := rfl

variable {H : Type} [CommRing H] [Algebra ℚ H]

def Geometry.AbelianH1Model.bettiHeckeAction (ρ : A.HeckeRealization H) : H →ₐ[ℚ] Module.End ℚ (A.Betti j) :=
  (A.rationalBettiAction j P).comp
    (ρ.action.toOpposite (fun h k => (Commute.all h k).map ρ.action.toMonoidHom))

theorem Geometry.AbelianH1Model.bettiHeckeAction_apply (ρ : A.HeckeRealization H) (h : H) :
    A.bettiHeckeAction j P ρ h = A.bettiHecke j ρ h := by
  classical
  change A.rationalBettiAction j P (MulOpposite.op (ρ.action h)) = _
  rw [← ρ.represents h]
  simp only [Finsupp.sum, Finset.op_sum, map_sum, Geometry.AbelianH1Model.rationalBettiAction_tmul]
  rfl

include P in
theorem Geometry.AbelianH1Model.bettiHecke_commute (ρ : A.HeckeRealization H) (h k : H) :
    Commute (A.bettiHecke j ρ h) (A.bettiHecke j ρ k) := by
  rw [← A.bettiHeckeAction_apply j P ρ h, ← A.bettiHeckeAction_apply j P ρ k]
  exact (Commute.all h k).map (A.bettiHeckeAction j P ρ).toMonoidHom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
