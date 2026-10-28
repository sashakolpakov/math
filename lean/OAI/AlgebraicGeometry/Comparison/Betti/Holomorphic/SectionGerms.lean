import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF

/-! # Section Germs -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionGerms.AnalyticLocal

noncomputable section

/-! Actual holomorphic sections determine germs, compatibly with open
restriction; every holomorphic germ has such a section representative. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite Set Filter
open scoped ContDiff _root_.Topology

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def holomorphicSectionGerm (U : Opens E) (x : E) (hx : x ∈ U) :
    FunctionPure.holomorphicFunctions U →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x where
  toFun f := ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x (CoefficientMem.openCoefficientExtension U f.val) U.isOpen hx
    ((show ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U f.val) (U : Set E) from f.property).differentiableOn
      (by norm_num))
  map_zero' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    change CoefficientMem.openCoefficientExtension U (0 : FunctionPure.holomorphicFunctions U).val y = 0
    rw [CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hy⟩]
    rfl
  map_one' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    change CoefficientMem.openCoefficientExtension U (1 : FunctionPure.holomorphicFunctions U).val y = 1
    rw [CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hy⟩]
    rfl
  map_add' f g := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    change CoefficientMem.openCoefficientExtension U (f + g).val y =
      CoefficientMem.openCoefficientExtension U f.val y + CoefficientMem.openCoefficientExtension U g.val y
    rw [CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hy⟩,
      CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hy⟩, CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hy⟩]
    rfl
  map_mul' f g := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    change CoefficientMem.openCoefficientExtension U (f * g).val y =
      CoefficientMem.openCoefficientExtension U f.val y * CoefficientMem.openCoefficientExtension U g.val y
    rw [CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hy⟩,
      CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hy⟩, CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hy⟩]
    rfl

theorem holomorphicSectionGerm_restrict {U V : Opens E} (h : V ≤ U) (x : E) (hx : x ∈ V) :
    (holomorphicSectionGerm V x hx).comp (Restrictions.holomorphicFunctionRestrict h).toRingHom =
      holomorphicSectionGerm U x (h hx) := by
  apply RingHom.ext
  intro f
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  filter_upwards [V.isOpen.mem_nhds hx] with y hy
  change CoefficientMem.openCoefficientExtension V (Restrictions.holomorphicFunctionRestrict h f).val y =
    CoefficientMem.openCoefficientExtension U f.val y
  rw [CoefficientMem.openCoefficientExtension_apply V _ ⟨y, hy⟩, CoefficientMem.openCoefficientExtension_apply U _ ⟨y, h hy⟩]
  rfl

theorem exists_holomorphicSectionGerm [FiniteDimensional ℂ E] (x : E) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) :
    ∃ (U : Opens E) (hx : x ∈ U) (f : FunctionPure.holomorphicFunctions U), holomorphicSectionGerm U x hx f = a := by
  obtain ⟨F, hFa, W, hW, hxW, hF⟩ := a.property
  let U : Opens E := ⟨W, hW⟩
  have hFsmooth := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn hW hF
  let f : FunctionPure.holomorphicFunctions U := ⟨fun y => F y, by
    apply hFsmooth.congr
    intro y hy
    exact CoefficientMem.openCoefficientExtension_apply U (fun y => F y) ⟨y, hy⟩⟩
  refine ⟨U, hxW, f, ?_⟩
  apply Subtype.ext
  change (CoefficientMem.openCoefficientExtension U f.val : Germ (𝓝 x) ℂ) = a.val
  rw [← hFa]
  apply Germ.coe_eq.mpr
  filter_upwards [hW.mem_nhds hxW] with y hy
  exact CoefficientMem.openCoefficientExtension_apply U f.val ⟨y, hy⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionGerms.AnalyticLocal
