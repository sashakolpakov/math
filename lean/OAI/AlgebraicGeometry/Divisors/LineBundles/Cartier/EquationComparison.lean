import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealEquationFrame
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ModuleHomOfBasis

/-! # Equation Comparison -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.EquationComparison.BundleCycles

noncomputable section

/-! Proportional local regular equations define an actual
isomorphism between the corresponding ideal sheaves. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Z Z' : Scheme.{0}} (i : Z ⟶ X) (j : Z' ⟶ X)
    (B : Set X.Opens) (hB : Opens.IsBasis B)
    (t u : ∀ U : B, Γ(X, U.1)) (ht : ∀ U, IsRegular (t U)) (hu : ∀ U, IsRegular (u U))
    (hkt : ∀ U, RingHom.ker (i.app U.1).hom = Ideal.span {t U})
    (hku : ∀ U, RingHom.ker (j.app U.1).hom = Ideal.span {u U})
    (hc : ∀ (U V : B) (h : U.1 ≤ V.1),
      t U * X.presheaf.map (homOfLE h).op (u V) = u U * X.presheaf.map (homOfLE h).op (t V))

def cartierEquationComparisonFrame (U : B) :
    Γ(LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i, U.1) ≃ₗ[Γ(X, U.1)] Γ(LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule j, U.1) :=
  (LineBundles.Scheme.IdealEquationFrame.BundleCycles.schemeIdealEquationFrame i U.1 (t U) (ht U) (hkt U)).trans
    (LineBundles.Scheme.IdealEquationFrame.BundleCycles.schemeIdealEquationFrame j U.1 (u U) (hu U) (hku U)).symm

theorem cartierEquationComparisonFrame_image (U : B) (m : Γ(LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i, U.1)) :
    LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear j U.1 (cartierEquationComparisonFrame i j B t u ht hu hkt hku U m) =
      LineBundles.Scheme.IdealEquationFrame.BundleCycles.schemeIdealEquationFrame i U.1 (t U) (ht U) (hkt U) m * u U := by
  rw [LineBundles.Scheme.IdealEquationFrame.BundleCycles.schemeIdealEquationFrame_image j U.1 (u U) (hu U) (hku U)]
  exact congrArg (fun r => r * u U)
    ((LineBundles.Scheme.IdealEquationFrame.BundleCycles.schemeIdealEquationFrame j U.1 (u U) (hu U) (hku U)).apply_symm_apply _)

include hc in
theorem cartierEquationComparisonFrame_restrict (U V : B) (h : U.1 ≤ V.1)
    (m : Γ(LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i, V.1)) :
    cartierEquationComparisonFrame i j B t u ht hu hkt hku U
        ((LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i).presheaf.map (homOfLE h).op m) =
      (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule j).presheaf.map (homOfLE h).op
        (cartierEquationComparisonFrame i j B t u ht hu hkt hku V m) := by
  apply LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_injective j U.1
  rw [cartierEquationComparisonFrame_image, LineBundles.Scheme.IdealEquationFrame.BundleCycles.schemeIdealModuleSectionLinear_restrict,
    cartierEquationComparisonFrame_image, map_mul]
  apply (ht U).left
  have hFrame := LineBundles.Scheme.IdealEquationFrame.BundleCycles.schemeIdealEquationFrame_restrict i U.1 V.1 h (t U) (t V) (ht U) (ht V)
    (hkt U) (hkt V) m
  let a := LineBundles.Scheme.IdealEquationFrame.BundleCycles.schemeIdealEquationFrame i U.1 (t U) (ht U) (hkt U)
    ((LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i).presheaf.map (homOfLE h).op m)
  let b := X.presheaf.map (homOfLE h).op (LineBundles.Scheme.IdealEquationFrame.BundleCycles.schemeIdealEquationFrame i V.1 (t V) (ht V) (hkt V) m)
  change t U * (a * u U) = t U * (b * X.presheaf.map (homOfLE h).op (u V))
  calc
    t U * (a * u U) = (a * t U) * u U := by ring
    _ = (b * X.presheaf.map (homOfLE h).op (t V)) * u U := congrArg (fun r => r * u U) hFrame
    _ = b * (u U * X.presheaf.map (homOfLE h).op (t V)) := by ring
    _ = b * (t U * X.presheaf.map (homOfLE h).op (u V)) := congrArg (fun r => b * r) (hc U V h).symm
    _ = t U * (b * X.presheaf.map (homOfLE h).op (u V)) := by ring

def cartierEquationComparisonHom : LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i ⟶ LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule j :=
  LineBundles.Scheme.ModuleHomOfBasis.BundleCycles.schemeModuleHomOfBasis (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i) (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule j) B hB
    (fun U => (cartierEquationComparisonFrame i j B t u ht hu hkt hku U).toLinearMap)
    (cartierEquationComparisonFrame_restrict i j B t u ht hu hkt hku hc)

theorem cartierEquationComparisonHom_isIso : IsIso (cartierEquationComparisonHom i j B hB t u ht hu hkt hku hc) :=
  LineBundles.Scheme.ModuleHomOfBasis.BundleCycles.schemeModuleHomOfBasis_isIso (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i) (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule j) B hB
    (fun U => (cartierEquationComparisonFrame i j B t u ht hu hkt hku U).toLinearMap)
    (cartierEquationComparisonFrame_restrict i j B t u ht hu hkt hku hc)
    (fun U => (cartierEquationComparisonFrame i j B t u ht hu hkt hku U).bijective)

def cartierEquationComparisonIso : LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i ≅ LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule j := by
  let : IsIso (cartierEquationComparisonHom i j B hB t u ht hu hkt hku hc) :=
    cartierEquationComparisonHom_isIso i j B hB t u ht hu hkt hku hc
  exact asIso (cartierEquationComparisonHom i j B hB t u ht hu hkt hku hc)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.EquationComparison.BundleCycles
