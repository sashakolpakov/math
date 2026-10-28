import OAI.AlgebraicGeometry.Divisors.LineBundles.IdealPullbackChartSurjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SurjectiveIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealBundle

/-! # Ideal Pullback Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso.BundleCycles

noncomputable section

/-! Actual Cartier ideal bundles commute with a pullback square
in which both closed subschemes have locally regular principal ideals. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Z X' Z' : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : Z' ⟶ X') [IsClosedImmersion j] (f : X' ⟶ X) (g : Z' ⟶ Z)
    (hp : IsPullback j g f i)
    (hi : IdealBundle.Cycles.HasRegularPrincipalImageIdeals i) (hj : IdealBundle.Cycles.HasRegularPrincipalImageIdeals j)

include hi hj in
theorem cartierIdealPullbackMap_isIso : IsIso (LineBundles.Scheme.IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g hp.w.symm) := by
  let B : Set X'.Opens := {V | IsAffineOpen V ∧ ∃ U : X.affineOpens, V ≤ f ⁻¹ᵁ U.1}
  have hB : Opens.IsBasis B := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro W x hx
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ W ⊓ f ⁻¹ᵁ U from ⟨hx, hxU⟩)
    exact ⟨V, ⟨hV, ⟨U, hU⟩, hVW.trans inf_le_right⟩, hxV, hVW.trans inf_le_left⟩
  apply LineBundle.SurjectiveIso.Cycles.lineBundleMorphism_isIso_of_basis_surjective
    ((IdealBundle.Cycles.cartierIdealLineBundle i hi).pullback f) (IdealBundle.Cycles.cartierIdealLineBundle j hj)
    (LineBundles.Scheme.IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g hp.w.symm) B hB
  rintro V ⟨hV, U, hVU⟩
  exact IdealPullbackChartSurjective.BundleCycles.schemeIdealPullback_affineChart_surjective i j f g hp U ⟨V, hV⟩ hVU

def cartierIdealPullbackIso :
    ((IdealBundle.Cycles.cartierIdealLineBundle i hi).pullback f).sheaf ≅ (IdealBundle.Cycles.cartierIdealLineBundle j hj).sheaf := by
  change (Scheme.Modules.pullback f).obj (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i) ≅ LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule j
  let : IsIso (LineBundles.Scheme.IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g hp.w.symm) :=
    cartierIdealPullbackMap_isIso i j f g hp hi hj
  exact asIso (LineBundles.Scheme.IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g hp.w.symm)

theorem cartierIdealPullbackIso_hom :
    (cartierIdealPullbackIso i j f g hp hi hj).hom = LineBundles.Scheme.IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g hp.w.symm := rfl

theorem cartierIdealPullbackIso_inclusion :
    (cartierIdealPullbackIso i j f g hp hi hj).hom ≫ LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion j =
      (Scheme.Modules.pullback f).map (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) ≫
        (LineBundle.OpenRestriction.Cycles.modulePullbackUnitIso f).hom :=
  LineBundles.Scheme.IdealPullbackMap.BundleCycles.schemeIdealPullbackMap_inclusion i j f g hp.w.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso.BundleCycles
