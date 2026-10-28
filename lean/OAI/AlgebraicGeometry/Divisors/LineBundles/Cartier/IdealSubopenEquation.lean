import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealEquation

/-! # Ideal Subopen Equation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealSubopenEquation.BundleCycles

noncomputable section

section

/-! A frame of the actual invertible ideal generates its full
equation ideal on every smaller open, allowing affine stalk computations. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (i : Z ⟶ X) [QuasiCompact i]
    (hi : IdealBundle.Cycles.HasRegularPrincipalImageIdeals i)

theorem cartierIdealSubopenEquation_kernel (x : X) (W : X.Opens)
    (hW : W ≤ (IdealBundle.Cycles.cartierIdealLineBundle i hi).trivializingOpen x) :
    RingHom.ker (i.app W).hom =
      Ideal.span {LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate (IdealBundle.Cycles.cartierIdealLineBundle i hi)
        (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW} := by
  let L := IdealBundle.Cycles.cartierIdealLineBundle i hi
  let e := L.sectionFrame x W hW
  apply le_antisymm
  · intro t ht
    let s := (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionsIso i W).inv ⟨t, ht⟩
    have h₁ := LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionsIso_inv_apply i W ⟨t, ht⟩
    have h₂ := LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate_apply L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW s
    exact Ideal.mem_span_singleton'.mpr ⟨e s, (h₁.symm.trans h₂).symm⟩
  · apply Ideal.span_le.mpr
    intro t ht
    rcases Set.mem_singleton_iff.mp ht with rfl
    change (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i).app W (e.symm 1) ∈ RingHom.ker (i.app W).hom
    rw [← LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply i W (e.symm 1)]
    exact LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_mem i W _

theorem cartierIdealSubopenEquation_ne_zero [IsIntegral X] (x : X) (W : X.Opens) [Nonempty W]
    (hW : W ≤ (IdealBundle.Cycles.cartierIdealLineBundle i hi).trivializingOpen x) :
    LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate (IdealBundle.Cycles.cartierIdealLineBundle i hi) (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW ≠ 0 := by
  intro ht
  have he := LineBundle.MorphismRationalCoordinate.Cycles.lineBundleMorphismFieldCoordinate_on_open (IdealBundle.Cycles.cartierIdealLineBundle i hi)
    (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW
  rw [ht, map_zero] at he
  exact IdealEquation.BundleCycles.cartierIdealMorphismFieldCoordinate_ne_zero i hi x he

end

/-! Every local frame of an actual Cartier ideal gives a regular
equation, including on arbitrary smaller opens. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem cartierIdealSubopenEquation_regular {X Z : Scheme.{0}}
    (i : Z ⟶ X) [QuasiCompact i] (hi : IdealBundle.Cycles.HasRegularPrincipalImageIdeals i)
    (x : X) (W : X.Opens)
    (hW : W ≤ (IdealBundle.Cycles.cartierIdealLineBundle i hi).trivializingOpen x) :
    IsRegular (LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate (IdealBundle.Cycles.cartierIdealLineBundle i hi)
      (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW) := by
  let L := IdealBundle.Cycles.cartierIdealLineBundle i hi
  let e := L.sectionFrame x W hW
  let t := LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW
  have hmap (a : Γ(X, W)) : LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear i W (e.symm a) = a * t := by
    have h := LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate_apply L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW (e.symm a)
    rw [e.apply_symm_apply] at h
    exact (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply i W (e.symm a)).trans h
  have hr : IsRightRegular t := by
    intro a b h
    apply e.symm.injective
    apply LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_injective i W
    exact (hmap a).trans (h.trans (hmap b).symm)
  exact ⟨fun a b h => hr ((mul_comm _ _).trans (h.trans (mul_comm _ _))), hr⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealSubopenEquation.BundleCycles
