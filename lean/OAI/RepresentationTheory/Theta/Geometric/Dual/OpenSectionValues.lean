import OAI.RepresentationTheory.Theta.Geometric.Dual.SectionTangentEvaluation
import OAI.RepresentationTheory.Theta.Geometric.ScalarFirstJet

/-! # Open Section Values -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues

noncomputable section

section

/-! Both coefficients of a native dual-number section value agree with
the actual scalar first jet along a holomorphic period map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

theorem dualGlobalSectionValue_fst {X : Scheme}
    (p : Spec (.of (DualNumber ℂ)) ⟶ X) (s : Γ(X, ⊤)) :
    (SectionEvaluation.dualGlobalSectionValue p s).fst =
      Complex.SectionEvaluation.complexSectionValue ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ).left ≫ p) ⊤ (by trivial) s := by
  have H := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction ℂ))) (p.appTop s)
  change (Scheme.ΓSpecIso (.of ℂ)).hom
    ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ).left.appTop (p.appTop s)) =
      (SectionEvaluation.dualGlobalSectionValue p s).fst at H
  change (SectionEvaluation.dualGlobalSectionValue p s).fst = (Scheme.ΓSpecIso (.of ℂ)).hom
    ((Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction ℂ)) ≫ p).appTop s)
  rw [Scheme.Hom.comp_appTop]
  exact H.symm

theorem nativeDualSectionValue_fst (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [Smooth X.hom]
    (s : Γ(X.left, ⊤)) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (v : TangentSpace (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p) :
    (SectionEvaluation.dualGlobalSectionValue (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val.left s).fst =
      RegularFunctionContinuity.regularFunctionValue X s p := by
  have H := congrArg Over.Hom.left (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).property
  exact (dualGlobalSectionValue_fst _ s).trans
    (Complex.SectionEvaluation.complexSectionValue_congr _ _ H ⊤ (by trivial) (by trivial) s)

theorem nativeDualSectionValue_firstJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (s : Γ(X.left, ⊤)) (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z) :
    SectionEvaluation.dualGlobalSectionValue (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X (p z)
      (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
        p z a)).val.left s = ScalarFirstJet.scalarFirstJet (RegularFunctionContinuity.regularFunctionValue X s ∘ p) z a := by
  apply TrivSqZeroExt.ext
  · exact nativeDualSectionValue_fst X s (p z) _
  · exact SectionTangentEvaluation.nativeDualSectionValue_periodDerivative X s p z a hp

end

/-! Evaluation of regular sections on an open at an actual dual-number
point, with restriction and pullback compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme}

def dualSectionValue (p : Spec (.of (DualNumber ℂ)) ⟶ X)
    (U : X.Opens) (hp : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ p ⁻¹ᵁ U) :
    Γ(X, U) →+* DualNumber ℂ :=
  (Scheme.ΓSpecIso (.of (DualNumber ℂ))).hom.hom.comp (p.appLE U ⊤ hp).hom

theorem dualSectionValue_congr (p q : Spec (.of (DualNumber ℂ)) ⟶ X) (h : p = q)
    (U : X.Opens) (hp : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ p ⁻¹ᵁ U)
    (hq : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ q ⁻¹ᵁ U) (s : Γ(X, U)) :
    dualSectionValue p U hp s = dualSectionValue q U hq s := by
  subst q
  rfl

theorem dualSectionValue_top (p : Spec (.of (DualNumber ℂ)) ⟶ X) (s : Γ(X, ⊤)) :
    dualSectionValue p ⊤ (by simp) s = SectionEvaluation.dualGlobalSectionValue p s := by
  have ht : p.appLE ⊤ ⊤ (by simp) = p.appTop := p.appLE_eq_app
  exact congrArg (fun f : Γ(X, ⊤) ⟶ Γ(Spec (.of (DualNumber ℂ)), ⊤) =>
    (Scheme.ΓSpecIso (.of (DualNumber ℂ))).hom (f s)) ht

theorem dualSectionValue_restrict (p : Spec (.of (DualNumber ℂ)) ⟶ X)
    (U W : X.Opens) (hWU : W ≤ U)
    (hp : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ p ⁻¹ᵁ W) (s : Γ(X, U)) :
    dualSectionValue p W hp (X.presheaf.map (homOfLE hWU).op s) =
      dualSectionValue p U (hp.trans (p.preimage_mono hWU)) s := by
  have H := p.map_appLE hp (homOfLE hWU).op
  exact congrArg (fun f : Γ(X, U) ⟶ Γ(Spec (.of (DualNumber ℂ)), ⊤) =>
    (Scheme.ΓSpecIso (.of (DualNumber ℂ))).hom (f s)) H

theorem dualSectionValue_pullback (p : Spec (.of (DualNumber ℂ)) ⟶ X) (f : X ⟶ Y)
    (U : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U)
    (hp : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ p ⁻¹ᵁ W) (s : Γ(Y, U)) :
    dualSectionValue p W hp (f.appLE U W hW s) =
      dualSectionValue (p ≫ f) U (hp.trans (p.preimage_mono hW)) s := by
  have H := Scheme.Hom.appLE_comp_appLE p f U W ⊤ hW hp
  exact congrArg (fun g : Γ(Y, U) ⟶ Γ(Spec (.of (DualNumber ℂ)), ⊤) =>
    (Scheme.ΓSpecIso (.of (DualNumber ℂ))).hom (g s)) H

theorem dualSectionValue_open (U : X.Opens)
    (p : Spec (.of (DualNumber ℂ)) ⟶ U.toScheme) (s : Γ(X, U)) :
    dualSectionValue (p ≫ U.ι) U (by
      intro t _
      exact (p t).property) s = SectionEvaluation.dualGlobalSectionValue p (U.topIso.inv s) := by
  have H := dualSectionValue_pullback p U.ι U ⊤ U.ι_preimage_self.ge (by simp) s
  have hm : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact congrArg X.presheaf.map (Subsingleton.elim _ _)
  rw [hm, dualSectionValue_top] at H
  exact H.symm

theorem dualSectionValue_fst (p : Spec (.of (DualNumber ℂ)) ⟶ X)
    (U : X.Opens) (hp : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ p ⁻¹ᵁ U)
    (s : Γ(X, U)) :
    (dualSectionValue p U hp s).fst =
      Complex.SectionEvaluation.complexSectionValue ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ).left ≫ p) U
        (hp (show (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
          (⊤ : (Spec (.of (DualNumber ℂ))).Opens) by trivial)) s := by
  have H := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction ℂ))) (p.appLE U ⊤ hp s)
  have hc := Scheme.Hom.appLE_comp_appLE
    (Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction ℂ))) p U ⊤ ⊤ hp (by simp)
  have hc' := congrArg (fun f : Γ(X, U) ⟶ Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) =>
    (Scheme.ΓSpecIso (.of ℂ)).hom (f s)) hc
  exact H.symm.trans hc'

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues
