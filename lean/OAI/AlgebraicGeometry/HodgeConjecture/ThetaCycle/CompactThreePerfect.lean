import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactThreePlanes
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactPlaneElimination

/-! # Compact Three Perfect -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactThreePerfect.CM

noncomputable section

/-! Compact unitary elimination proves perfectness of the actual SU(3)
group occurring at every compact real place. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

theorem compact_three_commutator_eq_top : commutator CompactThreePlanes.CM.CompactThreeGroup = ⊤ := by
  apply top_unique
  intro g _
  let x := g.val.val 0 2
  let y := g.val.val 1 2
  let z := g.val.val 2 2
  let r := Real.sqrt (Complex.normSq z + Complex.normSq x)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = Complex.normSq z + Complex.normSq x :=
    Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg z) (Complex.normSq_nonneg x))
  have hnorm : Complex.normSq x + Complex.normSq y + Complex.normSq z = 1 :=
    CompactThreePlanes.CM.compact_three_last_column_norm g
  obtain ⟨u0, h0, hcol0⟩ : ∃ u0 : CompactThreePlanes.CM.CompactThreeGroup,
      u0 ∈ commutator CompactThreePlanes.CM.CompactThreeGroup ∧ CompactThreePlanes.CM.compactThreeLastColumn (u0 * g) = ![0, y, (r : ℂ)] := by
    by_cases hr0 : r = 0
    · have hx : x = 0 := Complex.normSq_eq_zero.mp (by
        nlinarith [Complex.normSq_nonneg x, Complex.normSq_nonneg z])
      have hz : z = 0 := Complex.normSq_eq_zero.mp (by
        nlinarith [Complex.normSq_nonneg x, Complex.normSq_nonneg z])
      refine ⟨1, (commutator CompactThreePlanes.CM.CompactThreeGroup).one_mem, ?_⟩
      rw [one_mul, hr0]
      funext i
      fin_cases i
      · exact hx
      · rfl
      · change z = (0 : ℂ)
        exact hz
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      let p0 := CompactPlaneElimination.CM.compactPlaneEliminator x z r hrp hrsq.symm
      refine ⟨CompactThreePlanes.CM.compactThreePlane02 p0, CompactThreePlanes.CM.compact_plane_image_mem_commutator _ p0, ?_⟩
      rw [CompactThreePlanes.CM.compact_three_last_column_mul, CompactThreePlanes.CM.compact_three_plane02_vector]
      change ![(p0.val.val.mulVec ![x, z]) 0, y, (p0.val.val.mulVec ![x, z]) 1] = _
      rw [CompactPlaneElimination.CM.compact_plane_eliminator_action]
      rfl
  have hn1 : Complex.normSq (r : ℂ) + Complex.normSq y = (1 : ℝ) ^ 2 := by
    rw [Complex.normSq_ofReal]
    nlinarith
  let p1 := CompactPlaneElimination.CM.compactPlaneEliminator y (r : ℂ) 1 (by norm_num) hn1
  let u1 := CompactThreePlanes.CM.compactThreePlane12 p1
  have h1 : u1 ∈ commutator CompactThreePlanes.CM.CompactThreeGroup := CompactThreePlanes.CM.compact_plane_image_mem_commutator _ p1
  have hcol1 : CompactThreePlanes.CM.compactThreeLastColumn (u1 * (u0 * g)) = ![0, 0, 1] := by
    rw [CompactThreePlanes.CM.compact_three_last_column_mul, hcol0, CompactThreePlanes.CM.compact_three_plane12_vector]
    change ![0, (p1.val.val.mulVec ![y, (r : ℂ)]) 0,
      (p1.val.val.mulVec ![y, (r : ℂ)]) 1] = _
    rw [CompactPlaneElimination.CM.compact_plane_eliminator_action]
    simp
  have hk : u1 * (u0 * g) ∈ commutator CompactThreePlanes.CM.CompactThreeGroup :=
    CompactThreePlanes.CM.compact_three_vector_stabilizer_commutator _
      (congrFun hcol1 0) (congrFun hcol1 1) (congrFun hcol1 2)
  have h := (commutator CompactThreePlanes.CM.CompactThreeGroup).mul_mem ((commutator CompactThreePlanes.CM.CompactThreeGroup).inv_mem h0)
    ((commutator CompactThreePlanes.CM.CompactThreeGroup).mul_mem ((commutator CompactThreePlanes.CM.CompactThreeGroup).inv_mem h1) hk)
  simpa only [inv_mul_cancel_left] using h

theorem compact_three_character_eq_one {T : Type*} [CommGroup T]
    (χ : CompactThreePlanes.CM.CompactThreeGroup →* T) (g : CompactThreePlanes.CM.CompactThreeGroup) : χ g = 1 := by
  apply Abelianization.commutator_subset_ker χ
  rw [compact_three_commutator_eq_top]
  trivial

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactThreePerfect.CM
