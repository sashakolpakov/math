import OAI.RepresentationTheory.Theta.Geometric.Torus.Hom

/-! # Abelian Period Model Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.AbelianPeriodModelIso

noncomputable section

/-! Abelian models of the same period torus are canonically isomorphic. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom := A.variety.presentation.projective.isProper

theorem exists_abelian_period_iso (Φ : Torus.Data.CM.ProjectivePeriodData) (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eA : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (eB : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (hA : ∀ u v, eA (u + v) = eA u * eA v)
    (hB : ∀ u v, eB (u + v) = eB u * eB v) :
    ∃ e : A.toOver ≅ B.toOver, IsMonHom e.hom ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (eA t) = eB t := by
  let f : Φ.space →ₗ[ℂ] Φ.space := LinearMap.id
  have hf : ∀ v, v ∈ Φ.periodIntegerLattice → f v ∈ Φ.periodIntegerLattice := fun _ h => h
  have ht (t : Φ.periodTorus) : Torus.Hom.torusLinearMap Φ Φ f hf t = t := by
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
    rfl
  obtain ⟨g, hg, hgp⟩ := Torus.Hom.exists_algebraic_torus_map Φ Φ f hf A B eA eB hA hB
  obtain ⟨h, hh, hhp⟩ := Torus.Hom.exists_algebraic_torus_map Φ Φ f hf B A eB eA hB hA
  have hgp' (t) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (eA t) = eB t := (hgp t).trans (congrArg eB (ht t))
  have hhp' (t) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map h (eB t) = eA t := (hhp t).trans (congrArg eA (ht t))
  have hgh : g ≫ h = 𝟙 A.toOver := by
    apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
    intro p
    obtain ⟨t, rfl⟩ := eA.surjective p
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map h (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (eA t)) = eA t
    rw [hgp', hhp']
  have hhg : h ≫ g = 𝟙 B.toOver := by
    apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
    intro p
    obtain ⟨t, rfl⟩ := eB.surjective p
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map h (eB t)) = eB t
    rw [hhp', hgp']
  exact ⟨⟨g, h, hgh, hhg⟩, hg, hgp'⟩

end

end OAI.RepresentationTheory.Theta.Geometric.AbelianPeriodModelIso
