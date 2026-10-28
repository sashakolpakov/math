import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Transpose

/-! # Presheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Presheaf

noncomputable section

/-! Actual holomorphic forms and their exterior differentials form a presheaf of complexes. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def restrict {U V : Opens M} (h : U ≤ V) : DeRhamComplex.complex E V ⟶ DeRhamComplex.complex E U :=
  HolomorphicPullback.pullbackCochainMap (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, E)) (n := ∞) h)

theorem restrict_refl (U : Opens M) : restrict E M (le_refl U) = 𝟙 (DeRhamComplex.complex E U) :=
  HolomorphicPullback.pullbackCochainMap_id

theorem restrict_comp {U V W : Opens M} (hUV : U ≤ V) (hVW : V ≤ W) :
    restrict E M (hUV.trans hVW) = restrict E M hVW ≫ restrict E M hUV :=
  HolomorphicPullback.pullbackCochainMap_comp (Opens.inclusion hUV)
    (contMDiff_inclusion (I := 𝓘(ℂ, E)) (n := ∞) hUV) (Opens.inclusion hVW)
    (contMDiff_inclusion (I := 𝓘(ℂ, E)) (n := ∞) hVW)

def presheafOfComplexes : (Opens M)ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} ℂ) ℕ where
  obj U := DeRhamComplex.complex E U.unop
  map h := restrict E M (leOfHom h.unop)
  map_id U := restrict_refl E M U.unop
  map_comp f g := restrict_comp E M (leOfHom g.unop) (leOfHom f.unop)

def presheafComplex : CochainComplex ((Opens M)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ :=
  Complex.Transpose.transpose (presheafOfComplexes E M)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Presheaf
