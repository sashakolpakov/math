import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality

/-! # Map First Jet -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.MapFirstJet

noncomputable section

/-! The native dual-number first jet of a period parametrization is
local and natural for actual morphisms of smooth complex schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def nativeMapFirstJet (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : V) : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ X :=
  (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X (p z)
    (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      p z a)).val

set_option backward.isDefEq.respectTransparency false in
theorem nativeMapFirstJet_comp {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    (f : X ⟶ Y) (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z) :
    nativeMapFirstJet Y (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ p) z a = nativeMapFirstJet X p z a ≫ f := by
  have hn := AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality.nativeSchemeTangentDual_natural f (p z)
    (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z a)
  have hc := mfderiv_comp_apply z
    ((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f 1).mdifferentiableAt one_ne_zero) hp a
  change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv Y (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (p z))
    (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ p) z a)).val = _
  rw [hc]
  exact hn

set_option backward.isDefEq.respectTransparency false in
theorem nativeMapFirstJet_congr (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (p q : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : V) (h : p =ᶠ[𝓝 z] q) :
    nativeMapFirstJet X p z a = nativeMapFirstJet X q z a := by
  have ht : tangentMap (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p ⟨z, a⟩ =
      tangentMap (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) q ⟨z, a⟩ := by
    refine Bundle.TotalSpace.ext h.eq_of_nhds ?_
    rw [tangentMap, h.eq_of_nhds, tangentMap, h.mfderiv_eq]
    rfl
  exact congrArg (fun v : TangentBundle
    (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) => (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X v.1 v.2).val) ht

theorem nativeMapFirstJet_reduction (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : V) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ≫ nativeMapFirstJet X p z a = p z :=
  (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X (p z) _).property

theorem nativeMapFirstJet_open_range (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : V) (U : X.left.Opens)
    (hp : (p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U) :
    (⊤ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left.Opens) ≤ (nativeMapFirstJet X p z a).left ⁻¹ᵁ U := by
  let : Subsingleton (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberSpectrum.dualNumber_primeSpectrum_subsingleton
  intro t _
  have ht : t = (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) := Subsingleton.elim _ _
  have H := congrArg (fun f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => f.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
    (nativeMapFirstJet_reduction X p z a)
  change (nativeMapFirstJet X p z a).left t ∈ U
  exact (congrArg (nativeMapFirstJet X p z a).left ht).trans H ▸ hp

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.MapFirstJet
