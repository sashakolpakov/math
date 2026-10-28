import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ResidueDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

/-! # Fiber Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiberDegree

noncomputable section

/-! Affine primes over a target point are exactly the native scheme
fiber points, with identical residue-degree weights. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
  (hV : IsAffineOpen (f ⁻¹ᵁ U)) (y : Y) (hy : y ∈ U)

local instance : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra

def prime : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨y, hy⟩

theorem square : Spec.map (f.app U) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
  rw [Scheme.Hom.app_eq_appLE]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl

def point (q : (prime U hU y hy).asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)) : f ⁻¹' ({y} : Set Y) := by
  let Q : PrimeSpectrum Γ(X, f ⁻¹ᵁ U) := ⟨q.val, q.property.1⟩
  have hQ : (Spec.map (f.app U)) Q = prime U hU y hy := PrimeSpectrum.ext q.property.2.1.symm
  refine ⟨hV.fromSpec Q, ?_⟩
  change f (hV.fromSpec Q) = y
  have h := congrArg (fun k : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y => k Q) (square f U hU hV)
  exact h.symm.trans ((congrArg hU.fromSpec hQ).trans (hU.fromSpec_primeIdealOf ⟨y, hy⟩))

theorem injective : Function.Injective (point f U hU hV y hy) := by
  intro q q' he
  apply Subtype.ext
  have hp : hV.fromSpec (⟨q.val, q.property.1⟩ : PrimeSpectrum Γ(X, f ⁻¹ᵁ U)) =
      hV.fromSpec (⟨q'.val, q'.property.1⟩ : PrimeSpectrum Γ(X, f ⁻¹ᵁ U)) :=
    congrArg (fun x : f ⁻¹' ({y} : Set Y) => x.val) he
  have h := hV.fromSpec.isOpenEmbedding.injective hp
  exact congrArg PrimeSpectrum.asIdeal h

theorem surjective : Function.Surjective (point f U hU hV y hy) := by
  intro x
  have hxy : f x.val = y := x.property
  have hx : x.val ∈ f ⁻¹ᵁ U := by change f x.val ∈ U; rwa [hxy]
  let Q := hV.primeIdealOf ⟨x.val, hx⟩
  have hQ : (Spec.map (f.app U)) Q = prime U hU y hy := by
    apply hU.fromSpec.isOpenEmbedding.injective
    have h := congrArg (fun k : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y => k Q) (square f U hU hV)
    exact h.trans ((congrArg f (hV.fromSpec_primeIdealOf ⟨x.val, hx⟩)).trans
      (hxy.trans (hU.fromSpec_primeIdealOf ⟨y, hy⟩).symm))
  let q : (prime U hU y hy).asIdeal.primesOver Γ(X, f ⁻¹ᵁ U) :=
    ⟨Q.asIdeal, Q.isPrime, ⟨(congrArg PrimeSpectrum.asIdeal hQ).symm⟩⟩
  exact ⟨q, Subtype.ext (hV.fromSpec_primeIdealOf ⟨x.val, hx⟩)⟩

def equiv : (prime U hU y hy).asIdeal.primesOver Γ(X, f ⁻¹ᵁ U) ≃ f ⁻¹' ({y} : Set Y) :=
  Equiv.ofBijective (point f U hU hV y hy) ⟨FiberDegree.injective f U hU hV y hy, surjective f U hU hV y hy⟩

theorem degree (q : (prime U hU y hy).asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)) :
    f.residueDegree (point f U hU hV y hy q).val = q.val.inertiaDeg Γ(Y, U) := by
  let Q : PrimeSpectrum Γ(X, f ⁻¹ᵁ U) := ⟨q.val, q.property.1⟩
  change f.residueDegree (hV.fromSpec Q) = _
  rw [← Support.Map.residueDegree_pre_immersion hV.fromSpec f Q, ← square f U hU hV,
    Support.Map.residueDegree_post_immersion]
  exact ResidueDegree.residueDegree_eq_inertiaDeg Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Q

include hV in
theorem sum [Fintype (f ⁻¹' ({y} : Set Y))]
    [Fintype ((prime U hU y hy).asIdeal.primesOver Γ(X, f ⁻¹ᵁ U))] :
    ∑ x : f ⁻¹' ({y} : Set Y), f.residueDegree x.val =
      ∑ q : (prime U hU y hy).asIdeal.primesOver Γ(X, f ⁻¹ᵁ U), q.val.inertiaDeg Γ(Y, U) := by
  rw [← (equiv f U hU hV y hy).sum_comp (fun x => f.residueDegree x.val)]
  exact Finset.sum_congr rfl (fun q _ => degree f U hU hV y hy q)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiberDegree
