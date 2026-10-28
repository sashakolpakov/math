import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact
import OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphereHomology

/-! # Local Normal Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalNormalHomology.Cycles

noncomputable section

/-!
# Local singular homology of complex normal coordinates

The positive-degree connecting isomorphism of the actual pair
`(ℂ^p, ℂ^p \ {0})` combines with the explicit radial homotopy equivalence.
This reduces local homology in degrees at least two to homology of the actual
unit sphere. It does not assume or establish the computation of sphere homology,
a preferred generator, or an orientation-to-fundamental-class theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- For a complex normal model, the actual relative boundary identifies local
homology in degree `n+1` with punctured-space homology in positive degree `n`. -/
def complexNormalLocalBoundaryIso (p n : ℕ) (hn : n ≠ 0) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (n + 1) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ))) n :=
  RelativeHomologyExact.Cycles.relativeHomologyBoundaryIso (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n
    (ContractibleModel.Cycles.isZero_complexNormalModelHomology p (n + 1) (Nat.succ_ne_zero n))
    (ContractibleModel.Cycles.isZero_complexNormalModelHomology p n hn)

/-- The preceding isomorphism is the connecting boundary itself. -/
@[simp]
theorem complexNormalLocalBoundaryIso_hom (p n : ℕ) (hn : n ≠ 0) :
    (complexNormalLocalBoundaryIso p n hn).hom =
      RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n :=
  rfl

/-- Genuine local singular homology reduces to genuine unit-sphere homology by
the relative boundary followed by the explicitly constructed radial map. -/
def complexNormalLocalSphereIso (p n : ℕ) (hn : n ≠ 0) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (n + 1) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ))) n :=
  complexNormalLocalBoundaryIso p n hn ≪≫ NormalSphereHomology.Cycles.complexNormalSphereIntegralHomologyIso p n

/-- The local-to-sphere comparison uses the actual boundary and singular-homology
map induced by radial projection, rather than an arbitrarily chosen isomorphism. -/
@[simp]
theorem complexNormalLocalSphereIso_hom (p n : ℕ) (hn : n ≠ 0) :
    (complexNormalLocalSphereIso p n hn).hom =
      RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n ≫
        RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom (NormalSphere.Cycles.normalSphereProjection (Fin p → ℂ))) n :=
  rfl

/-- In every positive complex dimension `p+1`, the top local degree `2p+2`
reduces to sphere degree `2p+1`. No value of that sphere homology is assumed. -/
def positiveComplexNormalTopLocalSphereIso (p : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 (2 * p + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin (p + 1) → ℂ))) (2 * p + 1) :=
  complexNormalLocalSphereIso (p + 1) (2 * p + 1) (Nat.succ_ne_zero (2 * p))

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalNormalHomology.Cycles
