import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.FiniteBound
import OAI.AlgebraicGeometry.Resolution.Blowups.MinimalCoefficientBound

/-! # Minimal Coefficient Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A least shared coefficient bound yields either terminal ambient order or a proper next surface center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.terminal_of_uniform_bound_lt_factorial (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) {m : ℕ}
    (hb : ∀ i, (A.choice i).HasBound m) (hm : m < (n + 1).factorial) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤ := by
  apply Finite.OpenIdealSheafUniqueness.Construction.idealSheaf_eq_of_open_affine_restrictions (fun i => Spec (A.rings i)) A.map A.cover
  intro i
  rw [Scheme.IdealSheafData.comap_top]
  exact DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_unit_on_affine f J n (A.map i) (A.ground i)
    (A.ideals i) (A.ideal_eq i) ((A.choice i).terminal_of_bound_lt_factorial (hb i) hm)

omit [Smooth f] in
theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.exists_least_coefficient_bound (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hc : A.center = ⊤) :
    ∃ m, (∀ i, (A.choice i).HasBound m) ∧ ∀ r < m, ∃ i, ¬ (A.choice i).HasBound r := by
  classical
  have hex := A.exists_uniform_bound hc
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro r hr
  have h := Nat.find_min hex hr
  push Not at h
  exact h

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.exists_proper_surface_tangent_center
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hc : A.center = ⊤)
    (hn : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n ≠ ⊤) (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2) :
    ∃ ℓ, (n + 1).factorial ≤ ℓ + 1 ∧
      ∃ C : ∀ i, Surface.TangentCenterChoice.Construction.SurfaceTangentCenterChoice ℂ (A.rings i) (A.ideals i) n ℓ,
        ∃ I : X.IdealSheafData, I ≠ ⊤ ∧
          (∀ i, I.comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (C i).center) := by
  obtain ⟨m, hm, hmin⟩ := A.exists_least_coefficient_bound hc
  have hlevel : (n + 1).factorial ≤ m := by
    by_contra h
    exact hn (A.terminal_of_uniform_bound_lt_factorial hm (by omega))
  have hpos : 0 < m := lt_of_lt_of_le (Nat.factorial_pos (n + 1)) hlevel
  obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  let C (i : A.indices) := (A.choice i).toSurfaceTangentChoice ℓ (hm i)
  obtain ⟨I, hI, _⟩ := GlobalSurface.TangentGluing.Construction.existsUnique_global_surface_tangent_center ℂ f A.rings A.map A.ground A.cover
    J A.ideals A.ideal_eq n ℓ C hdim hlevel
  refine ⟨ℓ, hlevel, C, I, ?_, hI⟩
  intro ht
  obtain ⟨i, hi⟩ := hmin ℓ (Nat.lt_succ_self ℓ)
  apply hi
  apply ((A.choice i).tangentChoice_center_eq_top_iff (hm i)).mp
  have he := hI i
  rw [ht, Scheme.IdealSheafData.comap_top] at he
  apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
  exact he.symm.trans DifferentialUnitGluing.Construction.affineQuotientKernel_top.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
