import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPlaneGroups

/-! # Compact Three Planes -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactThreePlanes.CM

noncomputable section

section

/-! The actual compact SU(3) group and its three compact unitary planes. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

abbrev CompactThreeGroup := RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 3) (Fin 3) ℂ)

def compactThreePlane01 : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ) →* CompactThreeGroup :=
  (BallPlaneGroups.CM.sameSpecialUnitaryForm (UnitaryPlaneBlocks.CM.planeBlock 1 1) 1 UnitaryPlaneBlocks.CM.plane_block_one).comp (UnitaryPlaneBlocks.CM.unitaryPlaneBlock 1 1)

def compactThreeReindex (e : Equiv.Perm (Fin 3)) : CompactThreeGroup →* CompactThreeGroup :=
  (BallPlaneGroups.CM.sameSpecialUnitaryForm (Matrix.reindex e e 1) 1 (map_one (Matrix.reindexRingEquiv ℂ e))).comp
    (UnitaryPlaneBlocks.CM.reindexSpecialUnitary e 1)

def compactThreePlane02 : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ) →* CompactThreeGroup :=
  (compactThreeReindex (Equiv.swap 1 2)).comp compactThreePlane01

def compactThreePlane12 : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ) →* CompactThreeGroup :=
  (compactThreeReindex (Equiv.swap 0 1)).comp compactThreePlane02

theorem compact_three_plane01_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    (compactThreePlane01 g).val.val = UnitaryPlaneBlocks.CM.planeBlock g.val.val 1 := rfl

theorem compact_three_plane02_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    (compactThreePlane02 g).val.val =
      !![g.val.val 0 0, 0, g.val.val 0 1; 0, 1, 0; g.val.val 1 0, 0, g.val.val 1 1] := by
  change Matrix.reindex (Equiv.swap 1 2) (Equiv.swap 1 2) (UnitaryPlaneBlocks.CM.planeBlock g.val.val 1) = _
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindex_apply, UnitaryPlaneBlocks.CM.planeBlock, Equiv.swap_apply_def, Fin.ext_iff]

theorem compact_three_plane12_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    (compactThreePlane12 g).val.val =
      !![1, 0, 0; 0, g.val.val 0 0, g.val.val 0 1; 0, g.val.val 1 0, g.val.val 1 1] := by
  change Matrix.reindex (Equiv.swap 0 1) (Equiv.swap 0 1) (compactThreePlane02 g).val.val = _
  rw [compact_three_plane02_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.reindex_apply, Equiv.swap_apply_def, Fin.ext_iff]

theorem compact_plane_image_mem_commutator {G : Type*} [Group G]
    (f : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ) →* G) (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    f g ∈ commutator G := by
  apply SplitUnitaryPlane.CM.hom_maps_commutator
  rw [CompactPlanePerfect.CM.compact_plane_commutator_eq_top]
  trivial

def compactThreeLastColumn (g : CompactThreeGroup) : Fin 3 → ℂ := fun i => g.val.val i 2

theorem compact_three_last_column_mul (g h : CompactThreeGroup) :
    compactThreeLastColumn (g * h) = g.val.val.mulVec (compactThreeLastColumn h) := rfl

theorem compact_three_plane02_vector (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) (v : Fin 3 → ℂ) :
    (compactThreePlane02 p).val.val.mulVec v =
      ![(p.val.val.mulVec ![v 0, v 2]) 0, v 1, (p.val.val.mulVec ![v 0, v 2]) 1] := by
  rw [compact_three_plane02_matrix]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem compact_three_plane12_vector (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) (v : Fin 3 → ℂ) :
    (compactThreePlane12 p).val.val.mulVec v =
      ![v 0, (p.val.val.mulVec ![v 1, v 2]) 0, (p.val.val.mulVec ![v 1, v 2]) 1] := by
  rw [compact_three_plane12_matrix]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end

/-! The compact SU(3) last-column norm and its exact compact-plane
stabilizer, extracted from the actual unitary matrix equation. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

theorem compact_three_last_column_norm (g : CompactThreeGroup) :
    Complex.normSq (g.val.val 0 2) + Complex.normSq (g.val.val 1 2) +
      Complex.normSq (g.val.val 2 2) = 1 := by
  have hp : g.val.val.conjTranspose * 1 * g.val.val = 1 := g.property.1
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => (M 2 2).re) hp
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] at h ⊢
  nlinarith

theorem compact_three_vector_stabilizer (g : CompactThreeGroup)
    (h02 : g.val.val 0 2 = 0) (h12 : g.val.val 1 2 = 0) (h22 : g.val.val 2 2 = 1) :
    ∃ k : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ), compactThreePlane01 k = g := by
  have hp : g.val.val.conjTranspose * 1 * g.val.val = 1 := g.property.1
  have h20 : g.val.val 2 0 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 0) hp
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, h02, h12, h22] using h
  have h21 : g.val.val 2 1 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 1) hp
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, h02, h12, h22] using h
  let M : Matrix (Fin 2) (Fin 2) ℂ :=
    !![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1]
  have hblock : g.val.val = UnitaryPlaneBlocks.CM.planeBlock M 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [UnitaryPlaneBlocks.CM.planeBlock, M, h02, h12, h20, h21, h22]
  have hdet : M.det = 1 := by
    have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
    simpa only [hblock, UnitaryPlaneBlocks.CM.plane_block_det, mul_one] using hd
  have hform : M.conjTranspose * 1 * M = 1 := by
    apply Matrix.ext
    intro i j
    have h := congrArg (fun Q : Matrix (Fin 3) (Fin 3) ℂ => Q i.castSucc j.castSucc) hp
    fin_cases i <;> fin_cases j <;>
      simpa [M, Matrix.mul_apply, Fin.sum_univ_succ, h20, h21] using h
  refine ⟨SplitUnitaryPlane.CM.specialUnitaryOfMatrix 1 M hdet hform, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hblock.symm

theorem compact_three_vector_stabilizer_commutator (g : CompactThreeGroup)
    (h02 : g.val.val 0 2 = 0) (h12 : g.val.val 1 2 = 0) (h22 : g.val.val 2 2 = 1) :
    g ∈ commutator CompactThreeGroup := by
  obtain ⟨k, rfl⟩ := compact_three_vector_stabilizer g h02 h12 h22
  exact compact_plane_image_mem_commutator compactThreePlane01 k

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactThreePlanes.CM
