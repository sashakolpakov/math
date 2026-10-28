import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineResidueInjection
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleDegreeZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.ResidueVanishing

/-! # Empty Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyDegreeZero.Comparison

noncomputable section

/-! Vanishing and the common polynomial 1 for the original degree-zero cohomology of an empty scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem globalFunctions (Y : Scheme.{u}) [IsEmpty Y] : Subsingleton Γ(Y, ⊤) := by
  constructor
  intro s t
  exact TopCat.Presheaf.section_ext Y.sheaf ⊤ s t (fun y _ => isEmptyElim y)

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [IsEmpty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X 0
local notation "K" => FractionRing (WittVector p k)

include hprojective in
theorem integral : Subsingleton M := by
  let : Subsingleton Γ(X.left, ⊤) := globalFunctions X.left
  let : Subsingleton (ZeroLevel.GlobalFunctionLinear.coefficientModule p k X) := by
    constructor
    intro x y
    apply ULift.ext
    exact @Subsingleton.elim Γ(X.left, ⊤) inferInstance x.down y.down
  let : Module.Finite R M := SmoothProper.CrystallineFiniteness.integral_coefficient p k X hprojective 0
  let : IsAdicComplete (Ideal.span {(p : R)}) R := Witt.Coefficient.coefficient p k
  exact Zero.ResidueVanishing.subsingleton (Ideal.span {(p : R)}) (IsAdicComplete.le_jacobson_bot _)
    (SmoothProper.CrystallineResidueInjection.integralEvaluation p k X hprojective)
    (SmoothProper.CrystallineResidueInjection.integralEvaluation_kernel p k X hprojective)

include hprojective in
theorem rational : Subsingleton (Witt.Crystalline.rationalCohomology p k X 0) := by
  let := integral p k X hprojective
  exact inferInstanceAs (Subsingleton (TensorProduct (WittVector p k) K M))

omit p [Fact p.Prime] [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] in
theorem etale (ℓ : ℕ) [Fact ℓ.Prime] : Subsingleton (Interfaces.EtaleCohomology ℓ k X.hom 0) := by
  let : IsEmpty (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) X.hom) :=
    ⟨fun x => isEmptyElim (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) x)⟩
  exact (PeriodInvariants.EtaleDegreeZero.sectionsEquivQp ℓ _).injective.subsingleton

include hprojective in
theorem comparison (a : ℕ) (hcard : Fintype.card k = p ^ a) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (hcrys : FiniteDimensional K (Witt.Crystalline.rationalCohomology p k X 0))
      (het : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k X.hom 0)),
      letI := hcrys
      letI := het
      ∃ P : Polynomial ℤ, P.Monic ∧
        (Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0).charpoly = P.map (Int.castRingHom K) ∧
        (Interfaces.etaleGeometricFrobenius ℓ p a k hcard X.hom 0).charpoly = P.map (Int.castRingHom ℚ_[ℓ]) := by
  let := rational p k X hprojective
  let := etale k X ℓ
  refine ⟨inferInstance, inferInstance, 1, Polynomial.monic_one, ?_, ?_⟩
  · have hf : Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0 = 0 := Subsingleton.elim _ _
    rw [hf, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero, Polynomial.map_one]
  · have hf : Interfaces.etaleGeometricFrobenius ℓ p a k hcard X.hom 0 = 0 := Subsingleton.elim _ _
    rw [hf, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero, Polynomial.map_one]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyDegreeZero.Comparison
