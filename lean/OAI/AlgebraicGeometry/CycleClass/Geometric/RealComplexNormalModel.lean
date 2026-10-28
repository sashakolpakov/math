import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNormChange
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalNormalHomology
import Mathlib.Analysis.Complex.Basic

/-! # Real Complex Normal Model -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RealComplexNormalModel.Cycles

noncomputable section

/-!
# Explicit real coordinates on a complex normal model

Each complex coordinate is sent to its real and imaginary parts in that order.
The paired coordinates are then flattened to `Fin (2 * p)`. These are actual
continuous linear equivalences, so they give maps of the punctured spaces and
the relative singular-chain models. Radial retraction also gives the induced
comparison of unit-sphere homology, despite the different norms on the models.

This file does not identify a local homology generator with an orientation.
-/

open _root_.CategoryTheory

/-- A complex number in the ordered real coordinates `(Re, Im)`. -/
def complexCoordinatePair : ℂ ≃L[ℝ] (Fin 2 → ℝ) :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

@[simp]
theorem complexCoordinatePair_zero (z : ℂ) : complexCoordinatePair z 0 = z.re := rfl

@[simp]
theorem complexCoordinatePair_one (z : ℂ) : complexCoordinatePair z 1 = z.im := rfl

@[simp]
theorem complexCoordinatePair_symm_apply (x : Fin 2 → ℝ) :
    complexCoordinatePair.symm x = x 0 + x 1 * Complex.I := by
  change Complex.equivRealProdCLM.symm (x 0, x 1) = _
  exact Complex.equivRealProdCLM_symm_apply _

/-- The explicit real coordinate equivalence before flattening the indices. -/
def complexPairedRealEquiv (p : ℕ) :
    (Fin p → ℂ) ≃L[ℝ] (Fin p × Fin 2 → ℝ) where
  toFun z ij := complexCoordinatePair (z ij.1) ij.2
  invFun x i := complexCoordinatePair.symm (fun j ↦ x (i, j))
  left_inv z := by
    funext i
    exact complexCoordinatePair.symm_apply_apply (z i)
  right_inv x := by
    funext ij
    exact congrFun (complexCoordinatePair.apply_symm_apply (fun j ↦ x (ij.1, j))) ij.2
  map_add' z w := by
    funext ij
    exact congrFun (map_add complexCoordinatePair (z ij.1) (w ij.1)) ij.2
  map_smul' r z := by
    funext ij
    exact congrFun (map_smul complexCoordinatePair r (z ij.1)) ij.2
  continuous_toFun := by
    apply continuous_pi
    intro ij
    exact (continuous_apply ij.2).comp
      (complexCoordinatePair.continuous.comp (continuous_apply ij.1))
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply complexCoordinatePair.symm.continuous.comp
    exact continuous_pi fun j ↦ continuous_apply (i, j)

@[simp]
theorem complexPairedRealEquiv_apply (p : ℕ) (z : Fin p → ℂ) (i : Fin p) (j : Fin 2) :
    complexPairedRealEquiv p z (i, j) = complexCoordinatePair (z i) j := rfl

/-- The pair `(i,j)` becomes coordinate `2*i+j`; real and imaginary parts are
adjacent, rather than collected in two separate blocks. -/
def complexInterleavedIndex (p : ℕ) : Fin p × Fin 2 ≃ Fin (2 * p) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm p 2))

@[simp]
theorem complexInterleavedIndex_val (p : ℕ) (i : Fin p) (j : Fin 2) :
    (complexInterleavedIndex p (i, j)).val = 2 * i.val + j.val := by
  change j.val + 2 * i.val = 2 * i.val + j.val
  exact Nat.add_comm _ _

/-- Real and imaginary parts, in interleaved order, identify the complex
normal model with real Euclidean space of twice its dimension. -/
def complexRealEuclideanEquiv (p : ℕ) :
    (Fin p → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * p)) :=
  (complexPairedRealEquiv p).trans
    ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (2 * p) ↦ ℝ)
      (complexInterleavedIndex p)).trans
      (EuclideanSpace.equiv (Fin (2 * p)) ℝ).symm)

@[simp]
theorem complexRealEuclideanEquiv_apply_pair (p : ℕ) (z : Fin p → ℂ)
    (i : Fin p) (j : Fin 2) :
    complexRealEuclideanEquiv p z (complexInterleavedIndex p (i, j)) =
      complexCoordinatePair (z i) j := by
  change Equiv.piCongrLeft (fun _ : Fin (2 * p) ↦ ℝ) (complexInterleavedIndex p)
    (complexPairedRealEquiv p z) (complexInterleavedIndex p (i, j)) = _
  exact Equiv.piCongrLeft_apply_apply _ _ _ _

@[simp]
theorem complexRealEuclideanEquiv_apply_re (p : ℕ) (z : Fin p → ℂ) (i : Fin p) :
    complexRealEuclideanEquiv p z (complexInterleavedIndex p (i, 0)) = (z i).re := by
  rw [complexRealEuclideanEquiv_apply_pair, complexCoordinatePair_zero]

@[simp]
theorem complexRealEuclideanEquiv_apply_im (p : ℕ) (z : Fin p → ℂ) (i : Fin p) :
    complexRealEuclideanEquiv p z (complexInterleavedIndex p (i, 1)) = (z i).im := by
  rw [complexRealEuclideanEquiv_apply_pair, complexCoordinatePair_one]

/-- The inverse recombines each adjacent pair as `x + y I`. -/
theorem complexRealEuclideanEquiv_symm_apply (p : ℕ)
    (x : EuclideanSpace ℝ (Fin (2 * p))) (i : Fin p) :
    (complexRealEuclideanEquiv p).symm x i =
      x (complexInterleavedIndex p (i, 0)) +
        x (complexInterleavedIndex p (i, 1)) * Complex.I := by
  have hre := complexRealEuclideanEquiv_apply_re p ((complexRealEuclideanEquiv p).symm x) i
  have him := complexRealEuclideanEquiv_apply_im p ((complexRealEuclideanEquiv p).symm x) i
  rw [ContinuousLinearEquiv.apply_symm_apply] at hre him
  rw [hre, him]
  exact (Complex.re_add_im _).symm

/-- The explicit coordinate change restricts to the actual punctured spaces. -/
def complexRealPuncturedHomeomorph (p : ℕ) :
    NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ) ≃ₜ
      NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p))) :=
  NormalNormChange.Cycles.puncturedNormalHomeomorph (complexRealEuclideanEquiv p)

/-- The punctured-space homology comparison comes from the coordinate
homeomorphism itself. -/
def complexRealPuncturedHomologyIso (p n : ℕ) :
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ))) n ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p))))) n :=
  ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ)
    (X := TopCat.of (NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ)))
    (Y := TopCat.of (NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p)))))
    (complexRealPuncturedHomeomorph p).toHomotopyEquiv n

/-- Normalizing the interleaved coordinate change gives a homotopy equivalence
of the complex sup-norm sphere with the real Euclidean unit sphere. -/
def complexRealSphereHomotopyEquiv (p : ℕ) :
    ContinuousMap.HomotopyEquiv (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ))
      (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (2 * p)))) :=
  NormalNormChange.Cycles.normalSphereChange (complexRealEuclideanEquiv p)

theorem complexRealSphereHomotopyEquiv_apply_coe (p : ℕ)
    (x : NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ)) :
    ((complexRealSphereHomotopyEquiv p x :
      NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (2 * p)))) :
      EuclideanSpace ℝ (Fin (2 * p))) =
        ‖complexRealEuclideanEquiv p (x : Fin p → ℂ)‖⁻¹ •
          complexRealEuclideanEquiv p (x : Fin p → ℂ) :=
  NormalNormChange.Cycles.normalSphereChange_apply_coe (complexRealEuclideanEquiv p) x

/-- The homology comparison is induced by these explicit maps of spheres. -/
def complexRealSphereHomologyIso (p n : ℕ) :
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ))) n ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (2 * p))))) n :=
  NormalNormChange.Cycles.normalSphereHomologyChange (complexRealEuclideanEquiv p) n

@[simp]
theorem complexRealSphereHomologyIso_hom (p n : ℕ) :
    (complexRealSphereHomologyIso p n).hom =
      RelativeHomologyExact.Cycles.integralSingularHomologyMap
        (TopCat.ofHom (complexRealSphereHomotopyEquiv p).toFun) n := rfl

/-- The same coordinate change identifies the genuine local relative homology
groups, in every degree. -/
def complexRealLocalHomologyIso (p n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of (EuclideanSpace ℝ (Fin (2 * p)))) 0 n := by
  have hzero : (complexRealEuclideanEquiv p).toHomeomorph (0 : Fin p → ℂ) = 0 :=
    map_zero (complexRealEuclideanEquiv p)
  simpa only [hzero] using
    (LocalHomology.Cycles.localSingularHomologyIso
      (X := TopCat.of (Fin p → ℂ))
      (Y := TopCat.of (EuclideanSpace ℝ (Fin (2 * p))))
      (complexRealEuclideanEquiv p).toHomeomorph 0 n)

/-- In degrees at least two, the actual relative boundary and the explicit
coordinate/radial maps reduce complex local homology to a real unit sphere. -/
def complexNormalLocalRealSphereIso (p n : ℕ) (hn : n ≠ 0) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (n + 1) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (2 * p))))) n :=
  LocalNormalHomology.Cycles.complexNormalLocalSphereIso p n hn ≪≫ complexRealSphereHomologyIso p n

/-- The local-to-real-sphere map is the genuine relative boundary, followed
by the radial projection and the explicit coordinate comparison. -/
@[simp]
theorem complexNormalLocalRealSphereIso_hom (p n : ℕ) (hn : n ≠ 0) :
    (complexNormalLocalRealSphereIso p n hn).hom =
      RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n ≫
        RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom (NormalSphere.Cycles.normalSphereProjection (Fin p → ℂ))) n ≫
        RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom (complexRealSphereHomotopyEquiv p).toFun) n := by
  simp only [complexNormalLocalRealSphereIso, Iso.trans_hom,
    LocalNormalHomology.Cycles.complexNormalLocalSphereIso_hom, complexRealSphereHomologyIso_hom, Category.assoc]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RealComplexNormalModel.Cycles
