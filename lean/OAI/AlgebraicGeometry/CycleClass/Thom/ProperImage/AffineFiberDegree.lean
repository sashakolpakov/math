import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleFiberDegree
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Affine Fiber Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AffineFiberDegree.Constructions.Construction

noncomputable section

/-- The actual fiber of the affine complex-point map consists of
algebra homomorphisms over the point's scalar structure. -/
def affinePointFiberEquiv
    {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (h : A →ₐ[ℂ] B) (y : A →ₐ[ℂ] ℂ) :
    letI := h.toRingHom.toAlgebra
    letI := y.toRingHom.toAlgebra
    {x : B →ₐ[ℂ] ℂ // x.comp h = y} ≃ (B →ₐ[A] ℂ) := by
  let := h.toRingHom.toAlgebra
  let := y.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq' h.comp_algebraMap.symm
  let : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq' y.comp_algebraMap.symm
  refine
    { toFun := fun x =>
        { __ := x.1.toRingHom
          commutes' := fun a => AlgHom.congr_fun x.2 a }
      invFun := fun f => ⟨f.restrictScalars ℂ, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · ext a
    exact f.commutes a
  · intro x
    apply Subtype.ext
    ext b
    rfl
  · intro f
    ext b
    rfl

/-- Every complex fiber of a finite etale map of affine integral
complex varieties has cardinality equal to the generic algebra rank. -/
theorem card_affineEtale_fiber
    {A B : Type*} [CommRing A] [Algebra ℂ A] [IsDomain A]
    [CommRing B] [Algebra ℂ B]
    (h : A →ₐ[ℂ] B) (hf : h.toRingHom.Finite) (he : h.toRingHom.Etale)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Nat.card {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B // Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h x = y} =
      @Module.finrank A B _ _ h.toRingHom.toAlgebra.toModule := by
  let := h.toRingHom.toAlgebra
  let := y.toRingHom.toAlgebra
  let : Module.Finite A B := hf
  let : Algebra.Etale A B := he
  exact (Nat.card_congr (affinePointFiberEquiv h y)).trans (EtaleFiberDegree.Constructions.Construction.card_etale_point_lifts A B ℂ)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AffineFiberDegree.Constructions.Construction
