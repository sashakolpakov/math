import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPlaneGroups
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitPlaneElimination

/-! # Ball Perfect -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPerfect.CM

noncomputable section

section

/-! Explicit unitary elimination proves that the actual SU(2,1)
ball group is perfect. In particular all of its group characters vanish. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallNatural

def ballLastColumn (g : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup) : Fin 3 → ℂ := fun i => g.val.val i 2

theorem ball_last_column_mul (g h : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup) :
    ballLastColumn (g * h) = g.val.val.mulVec (ballLastColumn h) := rfl

theorem ball_split02_vector (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm) (v : Fin 3 → ℂ) :
    (BallPlaneGroups.CM.ballSplitPlane02 p).val.val.mulVec v =
      ![(p.val.val.mulVec ![v 0, v 2]) 0, v 1, (p.val.val.mulVec ![v 0, v 2]) 1] := by
  rw [BallPlaneGroups.CM.ball_split_plane02_matrix]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem ball_split12_vector (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm) (v : Fin 3 → ℂ) :
    (BallPlaneGroups.CM.ballSplitPlane12 p).val.val.mulVec v =
      ![v 0, (p.val.val.mulVec ![v 1, v 2]) 0, (p.val.val.mulVec ![v 1, v 2]) 1] := by
  rw [BallPlaneGroups.CM.ball_split_plane12_matrix]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem ball_group_commutator_eq_top : commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup = ⊤ := by
  apply top_unique
  intro g _
  let x := g.val.val 0 2
  let y := g.val.val 1 2
  let z := g.val.val 2 2
  let r := Real.sqrt (1 + Complex.normSq y)
  have hy : 0 < 1 + Complex.normSq y := by linarith [Complex.normSq_nonneg y]
  have hr : 0 < r := Real.sqrt_pos.mpr hy
  have hrsq : r ^ 2 = 1 + Complex.normSq y := Real.sq_sqrt hy.le
  have hnorm := BallPlaneGroups.CM.ball_last_column_norm g
  have hn0 : Complex.normSq z - Complex.normSq x = r ^ 2 := by
    change Complex.normSq z = 1 + Complex.normSq x + Complex.normSq y at hnorm
    linarith
  let p0 := SplitPlaneElimination.CM.splitPlaneEliminator x z r hr hn0
  let u0 := BallPlaneGroups.CM.ballSplitPlane02 p0
  have hcol0 : ballLastColumn (u0 * g) = ![0, y, (r : ℂ)] := by
    rw [ball_last_column_mul, ball_split02_vector]
    change ![(p0.val.val.mulVec ![x, z]) 0, y, (p0.val.val.mulVec ![x, z]) 1] = _
    rw [SplitPlaneElimination.CM.split_plane_eliminator_action]
    rfl
  have hn1 : Complex.normSq (r : ℂ) - Complex.normSq y = (1 : ℝ) ^ 2 := by
    rw [Complex.normSq_ofReal]
    nlinarith
  let p1 := SplitPlaneElimination.CM.splitPlaneEliminator y (r : ℂ) 1 (by norm_num) hn1
  let u1 := BallPlaneGroups.CM.ballSplitPlane12 p1
  have hcol1 : ballLastColumn (u1 * (u0 * g)) = ![0, 0, 1] := by
    rw [ball_last_column_mul, hcol0, ball_split12_vector]
    change ![0, (p1.val.val.mulVec ![y, (r : ℂ)]) 0,
      (p1.val.val.mulVec ![y, (r : ℂ)]) 1] = _
    rw [SplitPlaneElimination.CM.split_plane_eliminator_action]
    simp
  have hk : u1 * (u0 * g) ∈ commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup :=
    BallPlaneGroups.CM.ball_negative_vector_stabilizer_commutator _
      (congrFun hcol1 0) (congrFun hcol1 1) (congrFun hcol1 2)
  have h0 : u0 ∈ commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup := BallPlaneGroups.CM.ball_split_plane02_mem_commutator p0
  have h1 : u1 ∈ commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup := BallPlaneGroups.CM.ball_split_plane12_mem_commutator p1
  have h := (commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup).mul_mem ((commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup).inv_mem h0)
    ((commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup).mul_mem ((commutator RepresentationTheory.Theta.Adelic.BallNatural.BallGroup).inv_mem h1) hk)
  simpa only [inv_mul_cancel_left] using h

theorem ball_group_character_eq_one {T : Type*} [CommGroup T]
    (χ : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup →* T) (g : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup) : χ g = 1 := by
  apply Abelianization.commutator_subset_ker χ
  rw [ball_group_commutator_eq_top]
  trivial

end

/-! A lift of a perfect group automatically lies in the intrinsic bare
metaplectic subgroup. Apply this to the actual real ball group. -/

open OAI.RepresentationTheory.Theta.Adelic.BallNatural

theorem perfect_oscillator_lift_mem_metaplectic
    {G : Type*} [Group G] (hG : commutator G = ⊤)
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {n : ℕ} (ψ : AddChar k ℂ)
    (s : G →* RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k n ψ) (g : G) : s g ∈ RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
  have hg : g ∈ commutator G := by rw [hG]; trivial
  have hs := SplitUnitaryPlane.CM.hom_maps_commutator s hg
  have hle : commutator (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator k n ψ) ≤ RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
    rw [commutator_eq_closure]
    exact Subgroup.closure_mono Set.subset_union_left
  exact hle hs

theorem ball_oscillator_lift_mem_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {n : ℕ} (ψ : AddChar k ℂ)
    (s : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup →* RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k n ψ) (g : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup) :
    s g ∈ RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ :=
  perfect_oscillator_lift_mem_metaplectic ball_group_commutator_eq_top ψ s g

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPerfect.CM
