import OAI.AlgebraicGeometry.Comparison.Betti.SchemeHolomorphicLocalBases
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.RegularChartRestriction

/-! # Scheme Holomorphic Basis Neighborhoods -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SchemeHolomorphicBasisNeighborhoods

noncomputable section

/-! Actual algebraic-image bases can be chosen inside any prescribed analytic neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem schemePoint_algebraicImages_localBasis_within
    (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (p : O) (n : ℕ) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧
      ∃ (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hW : W ≤ Open.AffineIsoEvaluation.analyticOpen X U), W ≤ O ∧ (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ∈ W ∧
        ∃ I : Type, Finite I ∧
          ∃ b : Module.Basis I C^∞⟮𝓘(ℂ, RegularSmoothness.NativeModel X), W; 𝓘(ℂ), ℂ⟯ (Holomorphic.DeRhamComplex.forms (RegularSmoothness.NativeModel X) W n),
            ∀ i, ∃ a : Algebraic.Forms.Form Γ(X.left, U) n, b i =
              Holomorphic.HolomorphicPullback.pullback (Opens.inclusion hW) (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) hW) n
                ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a) := by
  obtain ⟨C, ⟨U, hU, e, he, rfl⟩, hp⟩ := ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.exists_schemeRegularChart X (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  obtain ⟨x, hx, hxp⟩ := hp
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x = (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) at hxp
  let S := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU ⁻¹' (O : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  have hS : IsOpen S := O.isOpen.preimage
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_affineOpenPointMap X U hU).continuous
  let er := e.restrOpen S hS
  have her := Affine.RegularChartRestriction.affineRegularAtlas_restrOpen e he S hS
  have hxr : x ∈ er.source := ⟨hx, by change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x ∈ O; rw [hxp]; exact p.property⟩
  obtain ⟨W, hW, hxW, hsource, I, hI, b, hb⟩ :=
    SchemeHolomorphicLocalBases.affineOpen_manifoldRealization_localBasis X U hU er her x hxr n
  refine ⟨U, hU, W, hW, ?_, ?_, I, hI, b, hb⟩
  · intro q hq
    obtain ⟨y, hy, rfl⟩ := hsource q hq
    exact hy.2
  · exact hxp ▸ hxW

end

end OAI.AlgebraicGeometry.Comparison.Betti.SchemeHolomorphicBasisNeighborhoods
