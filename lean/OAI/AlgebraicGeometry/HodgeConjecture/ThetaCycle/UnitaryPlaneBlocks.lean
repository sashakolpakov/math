import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitUnitaryPlane
import OAI.RepresentationTheory.Theta.Adelic.BallNatural

/-! # Unitary Plane Blocks -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryPlaneBlocks.CM

noncomputable section

/-! Explicit embeddings of two-dimensional unitary groups into the
three-dimensional matrix groups used at the real places. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

def planeBlock (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, t]

theorem plane_block_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) (s t : ℂ) :
    planeBlock M s * planeBlock N t = planeBlock (M * N) (s * t) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBlock, Matrix.mul_apply, Fin.sum_univ_succ]

theorem plane_block_star (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    (planeBlock M t).conjTranspose = planeBlock M.conjTranspose (star t) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [planeBlock]

theorem plane_block_one : planeBlock 1 1 = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [planeBlock]

theorem plane_block_det (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    (planeBlock M t).det = M.det * t := by
  simp [planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

def unitaryPlaneBlock (H : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (planeBlock H t) where
  toFun g := SplitUnitaryPlane.CM.specialUnitaryOfMatrix (planeBlock H t) (planeBlock g.val.val 1)
    (by
      have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
      rw [plane_block_det, hd, mul_one])
    (by
      rw [plane_block_star, plane_block_mul, plane_block_mul, star_one, one_mul, mul_one]
      exact congrArg (fun M => planeBlock M t) g.property.1)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact plane_block_one
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    change planeBlock (g.val.val * h.val.val) 1 = planeBlock g.val.val 1 * planeBlock h.val.val 1
    simpa only [mul_one] using (plane_block_mul g.val.val h.val.val 1 1).symm

def reindexSpecialUnitary (e : Equiv.Perm (Fin 3)) (H : Matrix (Fin 3) (Fin 3) ℂ) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (Matrix.reindex e e H) where
  toFun g := SplitUnitaryPlane.CM.specialUnitaryOfMatrix (Matrix.reindex e e H) (Matrix.reindex e e g.val.val)
    (by rw [Matrix.det_reindex_self]; exact congrArg Units.val g.property.2)
    (by
      have hp : g.val.val.conjTranspose * H * g.val.val = H := g.property.1
      have he := congrArg (Matrix.reindex e e) hp
      simpa only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.conjTranspose_submatrix] using he)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact map_one (Matrix.reindexRingEquiv ℂ e)
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    exact map_mul (Matrix.reindexRingEquiv ℂ e) g.val.val h.val.val

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryPlaneBlocks.CM
