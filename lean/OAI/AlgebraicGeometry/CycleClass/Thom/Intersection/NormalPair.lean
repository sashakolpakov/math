import OAI.AlgebraicGeometry.CycleClass.Thom.EquationNormalPair

/-! # Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalPair.Constructions

noncomputable section

/-! Simultaneous normal coordinates for an actual intersection. The
transversality condition is surjectivity of the derivative of the two
actual normal-coordinate functions taken together. -/

open scoped ContDiff _root_.Topology _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.EquationNormalPair.Constructions

variable {M L T N E F D G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  {p q : ℕ} {u : M → N} {v : L → N} {x : M} {y : L}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair F (Fin q → ℂ) v y)
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

def intersectionEquations (z : E × (Fin p → ℂ)) : Fin (p + q) → ℂ :=
  e (z.2, (Q.ambientChart (P.ambientChart.symm z)).2)

include P Q in
omit [FiniteDimensional ℂ E] in
theorem intersectionEquations_contDiffAt (hxy : u x = v y)
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hQ : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, F × (Fin q → ℂ)) ω
      Q.ambientChart Q.ambientChart.source) :
    ContDiffAt ℂ ω (intersectionEquations P Q e) 0 := by
  have h0 : (0 : E × (Fin p → ℂ)) ∈ P.ambientChart.target := by
    change (0, 0) ∈ P.ambientChart.target
    rw [← P.point_coordinates]
    exact P.ambientChart.map_source P.point_mem_source
  have hinv : P.ambientChart.symm 0 = u x := by
    change P.ambientChart.symm (0, 0) = u x
    rw [← P.point_coordinates, P.ambientChart.left_inv P.point_mem_source]
  have hQi : P.ambientChart.symm 0 ∈ Q.ambientChart.source := by
    rw [hinv, hxy]
    exact Q.point_mem_source
  have ha := (hQ _ hQi).contMDiffAt (Q.ambientChart.open_source.mem_nhds hQi)
  have hb := (hPi _ h0).contMDiffAt (P.ambientChart.open_target.mem_nhds h0)
  have hab : ContDiffAt ℂ ω (Q.ambientChart ∘ P.ambientChart.symm) 0 :=
    (ha.comp 0 hb).contDiffAt
  exact e.contDiff.contDiffAt.comp 0 (contDiffAt_snd.prodMk hab.snd)

theorem exists_intersection_normalPair (w : T → N) (z : T)
    (hxy : u x = v y) (hxz : u x = w z)
    (hw : Set.range w = Set.range u ∩ Set.range v)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hQ : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, F × (Fin q → ℂ)) ω
      Q.ambientChart Q.ambientChart.source)
    (hs : Function.Surjective (fderiv ℂ (intersectionEquations P Q e) 0))
    (k : (fderiv ℂ (intersectionEquations P Q e) 0).ker ≃L[ℂ] D) :
    ∃ R : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D (Fin (p + q) → ℂ) w z,
      R.neighborhood ⊆ P.neighborhood ∩ Q.neighborhood ∧
      R.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, D × (Fin (p + q) → ℂ)) ∧
      ∀ a : R.neighborhood, R.normalCoordinate a =
        e ((P.ambientChart a.val).2, (Q.ambientChart a.val).2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hxU : w z ∈ P.neighborhood ∩ Q.neighborhood := by
    rw [← hxz]
    exact ⟨P.point_mem_neighborhood, hxy ▸ Q.point_mem_neighborhood⟩
  have hcenter : P.ambientChart (w z) = 0 := hxz ▸ P.point_coordinates
  have heq : ∀ a ∈ P.neighborhood ∩ Q.neighborhood,
      a ∈ Set.range w ↔ intersectionEquations P Q e (P.ambientChart a) = 0 := by
    intro a ha
    rw [hw]
    change (a ∈ Set.range u ∧ a ∈ Set.range v) ↔ _
    rw [P.range_iff a ha.1, Q.range_iff a ha.2]
    unfold intersectionEquations
    rw [P.ambientChart.left_inv (P.neighborhood_subset_source ha.1),
      map_eq_zero_iff e e.injective]
    exact ⟨fun h => Prod.ext h.1 h.2,
      fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  obtain ⟨R, hRU, hRd, hRn⟩ := EquationNormalPair.Constructions.exists_equation_normalPair w z P.ambientChart hP
    (P.neighborhood ∩ Q.neighborhood) (P.isOpen_neighborhood.inter Q.isOpen_neighborhood)
    hxU (fun _ ha => P.neighborhood_subset_source ha.1) (intersectionEquations P Q e)
    (hcenter ▸ intersectionEquations_contDiffAt P Q e hxy hPi hQ)
    (hcenter ▸ hs) heq (hcenter ▸ k)
  refine ⟨R, hRU, hRd, ?_⟩
  intro a
  rw [hRn]
  unfold intersectionEquations
  rw [P.ambientChart.left_inv (P.neighborhood_subset_source (hRU a.property).1)]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalPair.Constructions
