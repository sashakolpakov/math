import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Fiber Scheme Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberSchemeIso

noncomputable section

/-! Isomorphisms over the original field transport geometric fibers and their actual pro-étale cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y)

def iso : Frobenius.Geometry.geometricFiber (L := L) X.hom ≅
    Frobenius.Geometry.geometricFiber (L := L) Y.hom := by
  let : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom)
  let : IsIso (FiberMap.map k L X.hom Y.hom e.hom.left e.hom.w) :=
    (FiberMap.isPullback k L X.hom Y.hom e.hom.left e.hom.w).isIso_fst_of_isIso
  exact asIso (FiberMap.map k L X.hom Y.hom e.hom.left e.hom.w)

omit L [Field L] [Algebra k L] in
def cohomology (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    Cohomology.RationalEllAdicCohomology ℓ
        (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) X.hom) i ≃ₗ[ℚ_[ℓ]]
      Cohomology.RationalEllAdicCohomology ℓ
        (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) Y.hom) i :=
  (Etale.Frobenius.cohomologyTransport ℓ (iso k (AlgebraicClosure k) e) i).restrictScalars ℚ_[ℓ]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberSchemeIso
