import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryPlaneBlocks
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactPlanePerfect

/-! # Ball Plane Groups -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPlaneGroups.CM

noncomputable section

section

/-! The compact (0,1) plane and the split (0,2) and (1,2) planes
inside the actual SU(2,1) ball group. -/

open scoped ComplexConjugate
open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallNatural

def sameSpecialUnitaryForm {n : Type*} [Fintype n] [DecidableEq n]
    (H H' : Matrix n n ℂ) (h : H = H') : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H' where
  toFun g := ⟨g.val, by
    constructor
    · rw [← h]; exact g.property.1
    · exact g.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def ballCompactPlane : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ) →* RepresentationTheory.Theta.Adelic.BallNatural.BallGroup :=
  (sameSpecialUnitaryForm (UnitaryPlaneBlocks.CM.planeBlock 1 (-1)) RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val (by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [UnitaryPlaneBlocks.CM.planeBlock, RepresentationTheory.Theta.Adelic.BallNatural.standardForm])).comp
      (UnitaryPlaneBlocks.CM.unitaryPlaneBlock 1 (-1))

def ballSplitPlane02 : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm →* RepresentationTheory.Theta.Adelic.BallNatural.BallGroup :=
  (sameSpecialUnitaryForm
    (Matrix.reindex (Equiv.swap 1 2) (Equiv.swap 1 2) (UnitaryPlaneBlocks.CM.planeBlock SplitUnitaryPlane.CM.splitPlaneForm 1))
    RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val (by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.reindex_apply, Equiv.swap_apply_def, Fin.ext_iff, UnitaryPlaneBlocks.CM.planeBlock,
          SplitUnitaryPlane.CM.splitPlaneForm, RepresentationTheory.Theta.Adelic.BallNatural.standardForm])).comp
      ((UnitaryPlaneBlocks.CM.reindexSpecialUnitary (Equiv.swap 1 2) (UnitaryPlaneBlocks.CM.planeBlock SplitUnitaryPlane.CM.splitPlaneForm 1)).comp
        (UnitaryPlaneBlocks.CM.unitaryPlaneBlock SplitUnitaryPlane.CM.splitPlaneForm 1))

def ballPositiveSwap : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup →* RepresentationTheory.Theta.Adelic.BallNatural.BallGroup :=
  (sameSpecialUnitaryForm
    (Matrix.reindex (Equiv.swap 0 1) (Equiv.swap 0 1) RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val) RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val (by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.reindex_apply, Equiv.swap_apply_def, Fin.ext_iff, RepresentationTheory.Theta.Adelic.BallNatural.standardForm])).comp
    (UnitaryPlaneBlocks.CM.reindexSpecialUnitary (Equiv.swap 0 1) RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val)

def ballSplitPlane12 : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm →* RepresentationTheory.Theta.Adelic.BallNatural.BallGroup := ballPositiveSwap.comp ballSplitPlane02

theorem ball_compact_plane_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    (ballCompactPlane g).val.val = UnitaryPlaneBlocks.CM.planeBlock g.val.val 1 := rfl

theorem ball_split_plane02_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm) :
    (ballSplitPlane02 g).val.val =
      !![g.val.val 0 0, 0, g.val.val 0 1; 0, 1, 0; g.val.val 1 0, 0, g.val.val 1 1] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ballSplitPlane02, sameSpecialUnitaryForm, UnitaryPlaneBlocks.CM.reindexSpecialUnitary,
      UnitaryPlaneBlocks.CM.unitaryPlaneBlock, SplitUnitaryPlane.CM.specialUnitaryOfMatrix, Matrix.reindex_apply, UnitaryPlaneBlocks.CM.planeBlock,
      Matrix.SpecialLinearGroup.toGL, Equiv.swap_apply_def, Fin.ext_iff]

theorem ball_split_plane12_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm) :
    (ballSplitPlane12 g).val.val =
      !![1, 0, 0; 0, g.val.val 0 0, g.val.val 0 1; 0, g.val.val 1 0, g.val.val 1 1] := by
  change Matrix.reindex (Equiv.swap 0 1) (Equiv.swap 0 1) (ballSplitPlane02 g).val.val = _
  rw [ball_split_plane02_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.reindex_apply, Equiv.swap_apply_def, Fin.ext_iff]

theorem ball_compact_plane_mem_commutator (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    ballCompactPlane g ∈ commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup := by
  apply SplitUnitaryPlane.CM.hom_maps_commutator
  rw [CompactPlanePerfect.CM.compact_plane_commutator_eq_top]
  trivial

theorem ball_split_plane02_mem_commutator (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm) :
    ballSplitPlane02 g ∈ commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup := by
  apply SplitUnitaryPlane.CM.hom_maps_commutator
  rw [SplitUnitaryPlane.CM.split_plane_commutator_eq_top]
  trivial

theorem ball_split_plane12_mem_commutator (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm) :
    ballSplitPlane12 g ∈ commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup := by
  apply SplitUnitaryPlane.CM.hom_maps_commutator
  rw [SplitUnitaryPlane.CM.split_plane_commutator_eq_top]
  trivial

def splitPlaneElement (a b : ℂ) (h : Complex.normSq a - Complex.normSq b = 1) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm := SplitUnitaryPlane.CM.specialUnitaryOfMatrix SplitUnitaryPlane.CM.splitPlaneForm !![a, b; conj b, conj a]
      (by simpa [Matrix.det_fin_two, Complex.mul_conj] using congrArg Complex.ofReal h)
      (by
        have hc : (Complex.normSq a : ℂ) - (Complex.normSq b : ℂ) = 1 :=
          by exact_mod_cast h
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [SplitUnitaryPlane.CM.splitPlaneForm, Matrix.mul_apply, Fin.sum_univ_two,
            Complex.mul_conj, mul_comm]
        all_goals first | linear_combination hc | linear_combination -hc)

end

/-! The stabilizer of the actual negative basis vector in SU(2,1)
is exactly the embedded compact special-unitary plane. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallNatural

theorem ball_last_column_norm (g : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup) :
    Complex.normSq (g.val.val 2 2) =
      1 + Complex.normSq (g.val.val 0 2) + Complex.normSq (g.val.val 1 2) := by
  have hp : g.val.val.conjTranspose * RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val * g.val.val = RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val := g.property.1
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => (M 2 2).re) hp
  simp [RepresentationTheory.Theta.Adelic.BallNatural.standardForm, Matrix.mul_apply, Fin.sum_univ_succ,
    Complex.mul_re, Complex.normSq_apply] at h ⊢
  nlinarith

theorem ball_negative_vector_stabilizer (g : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup)
    (h02 : g.val.val 0 2 = 0) (h12 : g.val.val 1 2 = 0) (h22 : g.val.val 2 2 = 1) :
    ∃ k : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (1 : Matrix (Fin 2) (Fin 2) ℂ), ballCompactPlane k = g := by
  have hp : g.val.val.conjTranspose * RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val * g.val.val = RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val := g.property.1
  have h20 : g.val.val 2 0 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 0) hp
    simpa [RepresentationTheory.Theta.Adelic.BallNatural.standardForm, Matrix.mul_apply, Fin.sum_univ_succ, h02, h12, h22] using h
  have h21 : g.val.val 2 1 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 1) hp
    simpa [RepresentationTheory.Theta.Adelic.BallNatural.standardForm, Matrix.mul_apply, Fin.sum_univ_succ, h02, h12, h22] using h
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
      simpa [M, RepresentationTheory.Theta.Adelic.BallNatural.standardForm, Matrix.mul_apply, Fin.sum_univ_succ, h20, h21] using h
  refine ⟨SplitUnitaryPlane.CM.specialUnitaryOfMatrix 1 M hdet hform, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hblock.symm

theorem ball_negative_vector_stabilizer_commutator (g : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup)
    (h02 : g.val.val 0 2 = 0) (h12 : g.val.val 1 2 = 0) (h22 : g.val.val 2 2 = 1) :
    g ∈ commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup := by
  obtain ⟨k, rfl⟩ := ball_negative_vector_stabilizer g h02 h12 h22
  exact ball_compact_plane_mem_commutator k

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPlaneGroups.CM
