import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartRestriction

/-! # Chart Transition -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartTransition.Construction

noncomputable section

/-! The chart quotient identifications commute with the actual infinitesimal transitions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

theorem infinitesimalTransition_chart_preimage (n : ℕ) (U : X.Opens) :
    Neighborhoods.Construction.infinitesimalTransition I f n ⁻¹ᵁ
        (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I (n + 1)) ⁻¹ᵁ U) =
      pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage]
  simp [Neighborhoods.Construction.infinitesimalTransition]

/-- Restriction along the actual infinitesimal transition, on the indicated chart. -/
def infinitesimalChartSectionTransition (n : ℕ) (U : X.Opens) :
    Γ(Neighborhoods.Construction.infinitesimalNeighborhood I f (n + 1),
      pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I (n + 1)) ⁻¹ᵁ U) ⟶
    Γ(Neighborhoods.Construction.infinitesimalNeighborhood I f n,
      pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U) :=
  (Neighborhoods.Construction.infinitesimalTransition I f n).appLE _ _
    (by rw [infinitesimalTransition_chart_preimage])

/-- The transition on the original chart quotients is induced by ideal-power inclusion. -/
def infinitesimalChartQuotientTransition (n : ℕ) (U : X.Opens) :
    CommRingCat.of (Γ(X, U) ⧸ (I ^ (n + 1 + 1)).map (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U)) ⟶
      CommRingCat.of (Γ(X, U) ⧸ (I ^ (n + 1)).map (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U)) :=
  CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.map_mono
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))

theorem infinitesimalChartSectionTransition_pullback (n : ℕ) (U : X.Opens) :
    (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I (n + 1))).app U ≫
        infinitesimalChartSectionTransition I f n U =
      (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)).app U := by
  rw [Scheme.Hom.app_eq_appLE, infinitesimalChartSectionTransition,
    Scheme.Hom.appLE_comp_appLE]
  simp [Neighborhoods.Construction.infinitesimalTransition, ← Scheme.Hom.app_eq_appLE]

/-- Actual infinitesimal restriction commutes with restricting a global function to a chart. -/
theorem infinitesimalChartSectionTransition_restrict_top (n : ℕ) (U : X.Opens) :
    (Neighborhoods.Construction.infinitesimalTransition I f n).appTop ≫
        (Neighborhoods.Construction.infinitesimalNeighborhood I f n).presheaf.map
          (homOfLE (show pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U ≤ ⊤ from le_top)).op =
      (Neighborhoods.Construction.infinitesimalNeighborhood I f (n + 1)).presheaf.map
        (homOfLE (show pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I (n + 1)) ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
          infinitesimalChartSectionTransition I f n U := by
  simp only [infinitesimalChartSectionTransition, Scheme.Hom.map_appLE,
    Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

/-- The geometric and quotient transition maps agree under the actual chart isomorphisms. -/
theorem affineInfinitesimalSectionsIso_transition (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    (Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso I f (n + 1) U hU).hom ≫
        infinitesimalChartSectionTransition I f n U =
      infinitesimalChartQuotientTransition I f n U ≫
        (Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso I f n U hU).hom := by
  ext s
  change infinitesimalChartSectionTransition I f n U
    ((Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso I f (n + 1) U hU).hom (Ideal.Quotient.mk _ s)) =
      (Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso I f n U hU).hom (Ideal.Quotient.mk _ s)
  rw [Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso_mk, Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso_mk]
  exact ConcreteCategory.congr_hom (infinitesimalChartSectionTransition_pullback I f n U) s

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartTransition.Construction
