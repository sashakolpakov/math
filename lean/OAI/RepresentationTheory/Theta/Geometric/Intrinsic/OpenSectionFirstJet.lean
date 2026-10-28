import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.MapFirstJet
import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues
import OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionHolomorphic
import OAI.RepresentationTheory.Theta.Geometric.ScalarFirstJetLocality

/-! # Open Section First Jet -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.OpenSectionFirstJet

noncomputable section

/-! The first jet of an original regular function on a native open is
its actual evaluation on the native dual-number period point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold _root_.Topology

set_option backward.isDefEq.respectTransparency false in
theorem nativeOpenSectionValue_firstJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (U : X.left.Opens) (s : Γ(X.left, U)) (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (hz : (p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U) :
    Dual.OpenSectionValues.dualSectionValue (MapFirstJet.nativeMapFirstJet X p z a).left U
      (MapFirstJet.nativeMapFirstJet_open_range X p z a U hz) s =
      ScalarFirstJet.scalarFirstJet (OpenRegularFunctionValues.openRegularFunctionValue X U s ∘ p) z a := by
  let Y := OpenRegularFunctionValues.regularOpenScheme X U
  let f := OpenRegularFunctionValues.regularOpenInclusion X U
  have hrange : p z ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion f]
    exact ⟨⟨(p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase), hz⟩, rfl⟩
  obtain ⟨q, hq⟩ := hrange
  let : Nonempty (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) := ⟨q⟩
  let : Nonempty Y.left := ⟨q.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)⟩
  let : IsIntegral Y.left := isIntegral_of_isOpenImmersion f.left
  let : Smooth Y.hom := inferInstanceAs (Smooth (U.ι ≫ X.hom))
  let h := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion f
  let e := h.toOpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
  let g := e.symm ∘ p
  have hg := OpenDifferentiableLift.mdifferentiableAt_nativeOpenInverse f p z hp ⟨q, hq⟩
  have hfac : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ g =ᶠ[𝓝 z] p := by
    have htarget : e.target = Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) :=
      h.toOpenPartialHomeomorph_target _
    filter_upwards [hp.continuousAt (e.open_target.mem_nhds (htarget.symm ▸ ⟨q, hq⟩))] with y hy
    exact h.toOpenPartialHomeomorph_right_inv _ (htarget ▸ hy)
  have hjet := congrArg Over.Hom.left ((MapFirstJet.nativeMapFirstJet_comp f g z a hg).symm.trans
    (MapFirstJet.nativeMapFirstJet_congr X _ p z a hfac))
  have hs : RegularFunctionContinuity.regularFunctionValue Y (U.topIso.inv s) ∘ g =ᶠ[𝓝 z]
      OpenRegularFunctionValues.openRegularFunctionValue X U s ∘ p := by
    filter_upwards [hfac] with y hy
    exact (OpenRegularFunctionValues.openRegularFunctionValue_inclusion X U s (g y)).symm.trans
      (congrArg (OpenRegularFunctionValues.openRegularFunctionValue X U s) hy)
  have hval := Dual.OpenSectionValues.dualSectionValue_congr _ _ hjet U
    (show (⊤ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left.Opens) ≤
      ((MapFirstJet.nativeMapFirstJet Y g z a).left ≫ U.ι) ⁻¹ᵁ U by intro t _; exact
        ((MapFirstJet.nativeMapFirstJet Y g z a).left t).property)
    (MapFirstJet.nativeMapFirstJet_open_range X p z a U hz) s
  exact hval.symm.trans ((Dual.OpenSectionValues.dualSectionValue_open U (MapFirstJet.nativeMapFirstJet Y g z a).left s).trans
    ((Dual.OpenSectionValues.nativeDualSectionValue_firstJet Y (U.topIso.inv s) g z a hg).trans
      (ScalarFirstJetLocality.scalarFirstJet_congr _ _ z a hs)))

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.OpenSectionFirstJet
