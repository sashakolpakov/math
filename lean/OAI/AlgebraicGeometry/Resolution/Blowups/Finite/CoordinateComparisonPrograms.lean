import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ChartProgramComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.UniformControlPrograms
import OAI.AlgebraicGeometry.Resolution.Blowups.EmptyBoundaryAtlas

/-! # Coordinate Comparison Programs -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CoordinateComparisonPrograms.Construction

noncomputable section

/-! A finite coordinate atlas shares actual common programs with one terminating global control-one program. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_global_control_one_with_coordinate_comparisons
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    {ι : Type} [Fintype ι] (x : ι → X) (C : ∀ i, Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J (x i)) :
    ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f J Y g K), K = ⊤ ∧
      ∀ i, Nonempty (Coordinate.ChartProgramComparison.Construction.CoordinateChartProgramComparison P (C i)) := by
  classical
  let κ := Unit ⊕ (ι ⊕ ι)
  let F : κ → Scheme
    | .inl _ => X
    | .inr (.inl i) => (C i).modelScheme
    | .inr (.inr i) => Spec (C i).ring
  let v : ∀ a, F a ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
    | .inl _ => f
    | .inr (.inl i) => (C i).modelStructure
    | .inr (.inr i) => (C i).map ≫ f
  let I : ∀ a, (F a).IdealSheafData
    | .inl _ => J
    | .inr (.inl i) => (C i).modelIdeal
    | .inr (.inr i) => J.comap (C i).map
  let : ∀ i, IsNoetherianRing (C i).ring := fun i => Algebra.FiniteType.isNoetherianRing ℂ (C i).ring
  let : ∀ a, IsIntegral (F a) := by
    intro a
    rcases a with _ | (i | i) <;> dsimp only [F] <;> infer_instance
  let : ∀ a, IsLocallyNoetherian (F a) := by
    intro a
    rcases a with _ | (i | i) <;> dsimp only [F] <;> infer_instance
  let : ∀ a, CompactSpace (F a) := by
    intro a
    rcases a with _ | (i | i) <;> dsimp only [F] <;> infer_instance
  let : ∀ a, Smooth (v a) := by
    intro a
    rcases a with _ | (i | i) <;> dsimp only [v] <;> infer_instance
  have hI (a : κ) : I a ≠ ⊥ := by
    rcases a with _ | (i | i)
    · exact hJ
    · exact (C i).modelIdeal_ne_bot
    · exact (C i).chartIdeal_ne_bot
  let D (a : κ) (_ : Fin 0) : (F a).IdealSheafData := ⊤
  let E (a : κ) : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (v a) (D a) [Finset.univ] := by
    convert Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.empty (v a) using 1
  obtain ⟨d, schedule, hprogram⟩ := UniformControlPrograms.Construction.exists_finite_uniform_control_programs 1 (by decide) F v I hI D E
  let 𝒮 := DimensionControlProgramSystems.Construction.finiteDimensionControlProgramSystem d
  obtain ⟨Y, g, K, P, HP⟩ := hprogram (.inl ())
  have hterminal : K = ⊤ := by
    have ht := 𝒮.terminal (by decide : 0 < 1) HP
    simpa only [Nat.sub_self, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_zero] using ht
  refine ⟨Y, g, K, P, hterminal, ?_⟩
  intro i
  obtain ⟨W, w, L, Q, HQ⟩ := hprogram (.inr (.inl i))
  obtain ⟨V, z, M, R, HR⟩ := hprogram (.inr (.inr i))
  have hsym := 𝒮.etaleSymmetric_of_unit_boundary HQ
  have hpattern : Q.UnitUntilWhole := hsym.unitUntilWhole_of_coordinate_model Q
    (𝟙 (C i).modelScheme) (Category.id_comp _) (Scheme.IdealSheafData.comap_id _)
  obtain ⟨r, hr⟩ := 𝒮.comparison HP HR (C i).map rfl rfl (fun _ => Scheme.IdealSheafData.comap_top _)
  obtain ⟨s, hs⟩ := 𝒮.comparison HQ HR (C i).modelMap (C i).modelMap_ground
    (C i).modelMap_ideal (fun _ => Scheme.IdealSheafData.comap_top _)
  exact ⟨⟨W, w, L, Q, hpattern, V, z, M, R, r, hr, s, hs⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CoordinateComparisonPrograms.Construction
