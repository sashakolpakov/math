import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.GeometricConnectedness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberEtaleDegreeZero

/-! # Etale Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.EtaleDegreeZero

noncomputable section

/-! The original geometric étale H⁰ and Frobenius reduce to the actual finite global-function algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Finite k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X

def base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

include hprojective in
omit [Finite k] [Smooth X.hom] in
theorem finite : IsFinite (base k X) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr
    (SmoothProper.GlobalFunctionAlgebra.module_finite k X hprojective))

variable (ℓ : ℕ) [Fact ℓ.Prime]

def equiv : Interfaces.EtaleCohomology ℓ k (base k X) 0 ≃ₗ[ℚ_[ℓ]] Interfaces.EtaleCohomology ℓ k X.hom 0 := by
  let := finite k X hprojective
  let := GeometricConnectedness.proper k X
  let := GeometricConnectedness.geometricallyConnected k X hprojective
  exact Geometric.FiberEtaleDegreeZero.equiv k X.hom (base k X)
    (WittFactor.affinization k X) (WittFactor.affinization_overBase k X) ℓ

variable (p a : ℕ) [Fact p.Prime] [Fintype k] [CharP k p] (hcard : Fintype.card k = p ^ a)

theorem frobenius (z : Interfaces.EtaleCohomology ℓ k (base k X) 0) :
    equiv k X hprojective ℓ (Interfaces.etaleGeometricFrobenius ℓ p a k hcard (base k X) 0 z) =
      Interfaces.etaleGeometricFrobenius ℓ p a k hcard X.hom 0 (equiv k X hprojective ℓ z) := by
  let := finite k X hprojective
  let := GeometricConnectedness.proper k X
  let := GeometricConnectedness.geometricallyConnected k X hprojective
  exact Geometric.FiberEtaleDegreeZero.automorphism k X.hom (base k X)
    (WittFactor.affinization k X) (WittFactor.affinization_overBase k X) ℓ
      (Frobenius.Geometry.geometricFrobenius p a k hcard) z

include hprojective in
theorem charpoly :
    letI := finite k X hprojective
    (Interfaces.etaleGeometricFrobenius ℓ p a k hcard X.hom 0).charpoly =
      (Interfaces.etaleGeometricFrobenius ℓ p a k hcard (base k X) 0).charpoly := by
  let := finite k X hprojective
  let := GeometricConnectedness.proper k X
  let := GeometricConnectedness.geometricallyConnected k X hprojective
  exact Geometric.FiberEtaleDegreeZero.charpoly k X.hom (base k X)
    (WittFactor.affinization k X) (WittFactor.affinization_overBase k X) ℓ
      (Frobenius.Geometry.geometricFrobenius p a k hcard)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.EtaleDegreeZero
