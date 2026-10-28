import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroPullbackIntertwining
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConnectedFiberDegreeZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleDegreeZero

/-! # Fiber Etale Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberEtaleDegreeZero

noncomputable section

/-! Original geometric étale H⁰ and its scalar automorphisms are preserved by actual proper geometrically connected maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX)
  [IsProper g] [GeometricallyConnected g] (ℓ : ℕ) [Fact ℓ.Prime]

def equiv : Interfaces.EtaleCohomology ℓ k fY 0 ≃ₗ[ℚ_[ℓ]] Interfaces.EtaleCohomology ℓ k fX 0 := by
  let m := FiberMap.map k (AlgebraicClosure k) fX fY g hg
  let : IsProper m := FiberMap.proper k (AlgebraicClosure k) fX fY g hg
  let : GeometricallyConnected m := FiberMap.geometricallyConnected k (AlgebraicClosure k) fX fY g hg
  exact Etale.ConnectedFiberDegreeZero.equiv m ℓ

theorem equiv_eq_pullback : (equiv k fX fY g hg ℓ).toLinearMap =
    PeriodInvariants.BigEtaleCohomology.pullbackQp ℓ (FiberMap.map k (AlgebraicClosure k) fX fY g hg) 0 := by
  let m := FiberMap.map k (AlgebraicClosure k) fX fY g hg
  let : IsProper m := FiberMap.proper k (AlgebraicClosure k) fX fY g hg
  let : GeometricallyConnected m := FiberMap.geometricallyConnected k (AlgebraicClosure k) fX fY g hg
  exact Etale.ConnectedFiberDegreeZero.equiv_eq_pullback m ℓ

variable (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)

theorem automorphism (z : Interfaces.EtaleCohomology ℓ k fY 0) :
    equiv k fX fY g hg ℓ (Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fY σ) z) =
      Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fX σ) (equiv k fX fY g hg ℓ z) := by
  have h := Etale.DegreeZeroPullbackIntertwining.cohomology
    (FiberMap.map k (AlgebraicClosure k) fX fY g hg)
    (Frobenius.Geometry.geometricFiberIso fX σ) (Frobenius.Geometry.geometricFiberIso fY σ)
    (FiberMap.scalar_natural k (AlgebraicClosure k) fX fY g hg σ) ℓ z
  have e := equiv_eq_pullback k fX fY g hg ℓ
  exact (congrArg (fun l => l (Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fY σ) z)) e).trans
    (h.trans (congrArg (Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fX σ))
      (congrArg (fun l => l z) e).symm))

theorem conjugate : (equiv k fX fY g hg ℓ).conj
    (Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fY σ)) =
      Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fX σ) := by
  let e := equiv k fX fY g hg ℓ
  apply LinearMap.ext
  intro z
  change e (Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fY σ) (e.symm z)) = _
  exact (automorphism k fX fY g hg ℓ σ (e.symm z)).trans
    (congrArg (Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fX σ)) (e.apply_symm_apply z))

include g hg in
theorem charpoly :
    (Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fX σ)).charpoly =
      (Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fY σ)).charpoly :=
  (congrArg (fun F : Module.End ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k fX 0) => F.charpoly)
    (conjugate k fX fY g hg ℓ σ).symm).trans
    ((equiv k fX fY g hg ℓ).charpoly_conj (Etale.ConnectedComponents.endomorphism ℓ _ (Frobenius.Geometry.geometricFiberIso fY σ)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberEtaleDegreeZero
