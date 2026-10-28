import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealBundle
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.MorphismRationalCoordinate
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealModule

/-! # Ideal Equation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealEquation.BundleCycles

noncomputable section

/-! The chosen frames of the actual invertible ideal give nonzero
local equations generating exactly the scheme-theoretic image ideals. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X) [QuasiCompact f]
    (hf : IdealBundle.Cycles.HasRegularPrincipalImageIdeals f)

def cartierIdealEquation (x : X) : Γ(X, (IdealBundle.Cycles.cartierIdealLineBundle f hf).trivializingOpen x) :=
  LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate (IdealBundle.Cycles.cartierIdealLineBundle f hf) (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f) x _ le_rfl

theorem cartierIdealEquation_image (x : X) :
    cartierIdealEquation f hf x =
      LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear f ((IdealBundle.Cycles.cartierIdealLineBundle f hf).trivializingOpen x)
        (((IdealBundle.Cycles.cartierIdealLineBundle f hf).sectionFrame x _ le_rfl).symm 1) :=
  (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply f _ _).symm

theorem cartierIdealEquation_kernel (x : X) :
    RingHom.ker (f.app ((IdealBundle.Cycles.cartierIdealLineBundle f hf).trivializingOpen x)).hom =
      Ideal.span {cartierIdealEquation f hf x} := by
  let L := IdealBundle.Cycles.cartierIdealLineBundle f hf
  let U := L.trivializingOpen x
  let e := L.sectionFrame x U le_rfl
  apply le_antisymm
  · intro t ht
    let s := (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionsIso f U).inv ⟨t, ht⟩
    have h : t = e s * cartierIdealEquation f hf x := by
      have h₁ := LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionsIso_inv_apply f U ⟨t, ht⟩
      have h₂ := LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate_apply L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f) x U le_rfl s
      exact h₁.symm.trans h₂
    exact Ideal.mem_span_singleton'.mpr ⟨e s, h.symm⟩
  · apply Ideal.span_le.mpr
    intro t ht
    rcases Set.mem_singleton_iff.mp ht with rfl
    rw [cartierIdealEquation_image]
    exact LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_mem f U _

theorem cartierIdealEquation_ne_zero [IsIntegral X] (x : X) : cartierIdealEquation f hf x ≠ 0 := by
  let L := IdealBundle.Cycles.cartierIdealLineBundle f hf
  let U := L.trivializingOpen x
  let e := L.sectionFrame x U le_rfl
  rw [cartierIdealEquation_image]
  intro ht
  have hm : e.symm 1 = 0 := (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_injective f U)
    (ht.trans (map_zero (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear f U)).symm)
  have he := congrArg e hm
  rw [e.apply_symm_apply, map_zero] at he
  exact one_ne_zero he

theorem cartierIdealMorphismFieldCoordinate_ne_zero [IsIntegral X] (x : X) :
    LineBundle.MorphismRationalCoordinate.Cycles.lineBundleMorphismFieldCoordinate (IdealBundle.Cycles.cartierIdealLineBundle f hf) (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f) x ≠ 0 :=
  (map_ne_zero_iff _ (X.germToFunctionField_injective ((IdealBundle.Cycles.cartierIdealLineBundle f hf).trivializingOpen x))).mpr
    (cartierIdealEquation_ne_zero f hf x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealEquation.BundleCycles
