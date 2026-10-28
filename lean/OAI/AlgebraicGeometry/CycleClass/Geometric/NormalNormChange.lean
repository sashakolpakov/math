import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphereHomology
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Normal Norm Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNormChange.Cycles

noncomputable section

/-!
# Changing the norm in local normal-space models

The ordinary function space `Fin p → ℂ` has the sup norm, whereas the Euclidean
model uses the `L²` norm. Their unit spheres are not definitionally the same.
An actual continuous linear equivalence identifies their punctured spaces;
the proved radial homotopy equivalences then identify their sphere homology.
No sphere-homology computation or orientation generator is assumed here.
-/

open _root_.CategoryTheory _root_.AlgebraicTopology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear coordinate change gives an actual homeomorphism of
the punctured normal spaces. -/
def puncturedNormalHomeomorph (e : E ≃L[ℝ] F) :
    NormalSphere.Cycles.PuncturedNormal E ≃ₜ NormalSphere.Cycles.PuncturedNormal F :=
  e.toHomeomorph.subtype (by
    intro x
    change x ≠ 0 ↔ e x ≠ 0
    constructor
    · intro hx he
      apply hx
      apply e.injective
      simpa only [map_zero] using he
    · intro hx he
      apply hx
      simp only [he, map_zero])

@[simp]
theorem puncturedNormalHomeomorph_apply (e : E ≃L[ℝ] F)
    (x : NormalSphere.Cycles.PuncturedNormal E) :
    ((puncturedNormalHomeomorph e x : NormalSphere.Cycles.PuncturedNormal F) : F) = e x := rfl

/-- Radial projection and inclusion transfer a change of normal coordinates
to a genuine homotopy equivalence of the corresponding unit spheres. -/
def normalSphereChange (e : E ≃L[ℝ] F) :
    ContinuousMap.HomotopyEquiv (NormalSphere.Cycles.NormalUnitSphere E) (NormalSphere.Cycles.NormalUnitSphere F) :=
  (NormalSphere.Cycles.normalSphereHomotopyEquiv E).symm.trans
    ((puncturedNormalHomeomorph e).toHomotopyEquiv.trans
      (NormalSphere.Cycles.normalSphereHomotopyEquiv F))

/-- The forward map is the normalized linear coordinate change. -/
theorem normalSphereChange_apply_coe (e : E ≃L[ℝ] F) (x : NormalSphere.Cycles.NormalUnitSphere E) :
    ((normalSphereChange e x : NormalSphere.Cycles.NormalUnitSphere F) : F) =
      ‖e (x : E)‖⁻¹ • e (x : E) := by
  change ((NormalSphere.Cycles.normalSphereProjection F
    (puncturedNormalHomeomorph e (NormalSphere.Cycles.normalSphereInclusion E x)) : NormalSphere.Cycles.NormalUnitSphere F) : F) = _
  rw [NormalSphere.Cycles.normalSphereProjection_coe, puncturedNormalHomeomorph_apply,
    NormalSphere.Cycles.normalSphereInclusion_coe]

/-- The resulting sphere-homology isomorphism is induced by actual maps. -/
def normalSphereHomologyChange (e : E ≃L[ℝ] F) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))).homology n ≅
      (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere F))).homology n :=
  ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ)
    (X := TopCat.of (NormalSphere.Cycles.NormalUnitSphere E)) (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere F))
    (normalSphereChange e) n

/-- The genuine real continuous linear equivalence between sup-norm complex
coordinates and their Euclidean version. -/
def complexPiEuclideanRealEquiv (p : ℕ) :
    (Fin p → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin p) where
  toLinearEquiv := (EuclideanSpace.equiv (Fin p) ℂ).symm.toLinearEquiv.restrictScalars ℝ
  continuous_toFun := (EuclideanSpace.equiv (Fin p) ℂ).symm.continuous
  continuous_invFun := (EuclideanSpace.equiv (Fin p) ℂ).continuous

/-- The sup-norm and Euclidean-norm complex coordinate spheres have the same
homotopy type through explicitly constructed radial maps. -/
def complexEuclideanSphereChange (p : ℕ) :
    ContinuousMap.HomotopyEquiv (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ))
      (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℂ (Fin p))) :=
  normalSphereChange (complexPiEuclideanRealEquiv p)

/-- In particular their actual integral singular homology groups are isomorphic. -/
def complexEuclideanSphereHomologyChange (p n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ)))).homology n ≅
      (LocalHomology.Cycles.integralSingularChains
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℂ (Fin p))))).homology n :=
  normalSphereHomologyChange (complexPiEuclideanRealEquiv p) n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNormChange.Cycles
