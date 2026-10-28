import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.PointCoproduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.GeometricFiber
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittSplitting
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleDegreeZero

/-! # Higher -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.Higher.Etale

noncomputable section

/-! All positive-degree original geometric pro-étale cohomology of a finite étale algebra vanishes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable (k A : Type u) [Field k] [CommRing A] [Algebra k A]
  [Module.Finite k A] [Algebra.Etale k A]

local notation "Ω" => AlgebraicClosure k
local notation "T" => Ω ⊗[k] A
local notation "f" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "Y" => OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry.geometricFiber (L := Ω) f
local notation "P" => (fun _ : PrimeSpectrum T => Spec (CommRingCat.of Ω))

local instance : Finite (PrimeSpectrum T) := WittSplitting.finite_index k A
local instance : IsFinite f :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

def splitting : Y ≅ ∐ P :=
  Affine.GeometricFiber.iso k A ≪≫
    (Scheme.Spec.mapIso (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω T).toRingEquiv.toCommRingCatIso.op).symm ≪≫
      (asIso (sigmaSpec (fun _ : PrimeSpectrum T => CommRingCat.of Ω))).symm

variable (ℓ : ℕ) [Fact ℓ.Prime]

def equiv (n : ℕ) : Interfaces.EtaleCohomology ℓ k f n ≃ₗ[ℚ_[ℓ]]
    Cohomology.RationalEllAdicCohomology ℓ (∐ P) n :=
  (IntegralComparison.Etale.Frobenius.cohomologyTransport ℓ (splitting k A) n).restrictScalars ℚ_[ℓ]

theorem vanishing (n : ℕ) : Subsingleton (Interfaces.EtaleCohomology ℓ k f (n + 1)) := by
  let := Geometric.PointCoproduct.vanishing (PrimeSpectrum T) (fun _ => Ω) ℓ n
  exact (equiv k A ℓ (n + 1)).injective.subsingleton

theorem finite (n : ℕ) : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f n) := by
  cases n with
  | zero => exact SmoothProper.EtaleDegreeZero.finite k f ℓ
  | succ n =>
    let := vanishing k A ℓ n
    infer_instance

theorem charpoly (n : ℕ) (F : Module.End ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f (n + 1))) :
    letI := finite k A ℓ (n + 1)
    F.charpoly = 1 := by
  let := vanishing k A ℓ n
  have h : F = 0 := Subsingleton.elim _ _
  rw [h, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.Higher.Etale
