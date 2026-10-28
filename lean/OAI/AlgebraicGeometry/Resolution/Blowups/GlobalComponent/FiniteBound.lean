import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBounds
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Center
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.TangentGluing

/-! # Finite Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent

noncomputable section

/-! A unit global component center yields a finite shared coefficient bound on its actual atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.exists_uniform_bound (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hc : A.center = ⊤) :
    ∃ m, ∀ i, (A.choice i).HasBound m := by
  let : ∀ i, IsNoetherianRing (A.rings i) := fun i => Algebra.FiniteType.isNoetherianRing ℂ (A.rings i)
  apply Component.ChoiceBounds.Construction.exists_uniform_component_choice_bound ℂ (fun i => A.rings i) A.ideals n A.choice
  intro i
  have h := A.center_restrict i
  rw [hc, Scheme.IdealSheafData.comap_top] at h
  have ht : Affine.QuotientKernel.Construction.affineQuotientKernel (⊤ : Ideal (A.rings i)) = ⊤ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop, Ideal.comap_top]
    rfl
  exact (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp (h.symm.trans ht.symm)

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.exists_surface_tangent_center (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    (hc : A.center = ⊤) (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2) :
    ∃ ℓ, (n + 1).factorial ≤ ℓ + 1 ∧
      ∃ C : ∀ i, Surface.TangentCenterChoice.Construction.SurfaceTangentCenterChoice ℂ (A.rings i) (A.ideals i) n ℓ,
        ∃! I : X.IdealSheafData, ∀ i, I.comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (C i).center := by
  obtain ⟨m, hm⟩ := A.exists_uniform_bound hc
  let ℓ := m + (n + 1).factorial
  have hl : (n + 1).factorial ≤ ℓ + 1 := by omega
  let C (i : A.indices) := (A.choice i).toSurfaceTangentChoice ℓ
    ((A.choice i).hasBound_mono (hm i) (show m ≤ ℓ + 1 by omega))
  refine ⟨ℓ, hl, C, ?_⟩
  exact GlobalSurface.TangentGluing.Construction.existsUnique_global_surface_tangent_center ℂ f A.rings A.map A.ground A.cover
    J A.ideals A.ideal_eq n ℓ C hdim hl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent
