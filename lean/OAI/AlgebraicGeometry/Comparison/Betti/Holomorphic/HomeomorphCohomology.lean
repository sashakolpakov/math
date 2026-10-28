import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HomeomorphSections
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCohomology

/-! # Homeomorph Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HomeomorphCohomology.Dolbeault

noncomputable section

/-! Native holomorphic function cohomology is invariant under the proved
sheaf identification associated to a biholomorphic homeomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  (e : M ≃ₜ N) (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ e)
  (he' : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ∞ e.symm)

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)) :=
  HasExt.standard _
local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)) :=
  HasExt.standard _

def holomorphicHomeomorphExtEquiv (q : ℕ) :
    Abelian.Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
        (ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M) q ≃
      Abelian.Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of N))
        (ScalarSheaf.Dolbeault.holomorphicScalarSheaf F N) q := by
  obtain ⟨a, _⟩ := NumberTheory.PadicHodge.IntegralComparison.ZariskiHomeomorphism.cohomologyEquiv e (ModuleCat.{0} ℂ)
    (ModuleCat.of ℂ ℂ) (ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M) q
  let b := SheafCohomology.Ext.Projective.extRightIso ℂ (ConstantSheafSections.standardConstantSheaf (TopCat.of N))
    (HomeomorphSections.Dolbeault.holomorphicHomeomorphSheafIso e he he') q
  obtain ⟨⟨⟨f, _⟩, _⟩, g, hl, hr⟩ := b
  exact a.trans ⟨f, g, hl, hr⟩

def holomorphicHomeomorphCohomologyEquiv (q : ℕ) :
    Sheaf.H.{0} (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) q ≃
      Sheaf.H.{0} (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf F N) q := by
  obtain ⟨a, _⟩ := Complex.SheafCohomology.complexSheafCohomologyForgetEquiv (TopCat.of M)
    (ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M) q
  obtain ⟨b, _⟩ := Complex.SheafCohomology.complexSheafCohomologyForgetEquiv (TopCat.of N)
    (ScalarSheaf.Dolbeault.holomorphicScalarSheaf F N) q
  exact a.symm.trans ((holomorphicHomeomorphExtEquiv e he he' q).trans b)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HomeomorphCohomology.Dolbeault
