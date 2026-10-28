import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalSection
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: genuine finite divisors of rational sections of algebraic line bundles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.finite_support_rationalSectionOrder : (Function.support L.rationalSectionOrder).Finite := by
  have : Nonempty L.rationalReferenceOpen := ⟨⟨genericPoint X, L.mem_trivializingOpen _⟩⟩
  apply (Ord.BundleCycles.finite_codimension_one_complement X L.rationalReferenceOpen).subset
  intro x hx
  constructor
  · by_contra hc
    exact hx (L.rationalSectionOrder_eq_zero_of_coheight_ne_one x hc)
  · intro hu
    exact hx (L.rationalSectionOrder_zero_on_reference x hu)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointDivisor : X →₀ ℤ :=
  Finsupp.ofSupportFinite L.rationalSectionOrder L.finite_support_rationalSectionOrder

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointDivisor_apply (x : X) : L.rationalSectionPointDivisor x = L.rationalSectionOrder x := rfl

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycle : X →₀ ℚ :=
  L.rationalSectionPointDivisor.mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycle_apply (x : X) : L.rationalSectionPointCycle x = (L.rationalSectionOrder x : ℚ) := rfl

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycle_coheight (x : X) (hx : L.rationalSectionPointCycle x ≠ 0) : coheight x = 1 := by
  by_contra hc
  apply hx
  rw [LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycle_apply, L.rationalSectionOrder_eq_zero_of_coheight_ne_one x hc, Int.cast_zero]

/-- Multiplying the actual rational section by a nonzero rational coefficient. -/
def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointDivisorWithCoefficient (a : X.functionFieldˣ) : X →₀ ℤ :=
  Ord.BundleCycles.principalDivisor X a.val + L.rationalSectionPointDivisor

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointDivisorWithCoefficient_apply (a : X.functionFieldˣ) (x : X) :
    L.rationalSectionPointDivisorWithCoefficient a x =
      X.ord (a.val * (L.rationalSectionCoordinate x).val) x := by
  exact (Scheme.ord_mul a.ne_zero (L.rationalSectionCoordinate_ne_zero x)).symm

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycleWithCoefficient (a : X.functionFieldˣ) : X →₀ ℚ :=
  (L.rationalSectionPointDivisorWithCoefficient a).mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycleWithCoefficient_eq (a : X.functionFieldˣ) :
    L.rationalSectionPointCycleWithCoefficient a = RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X a.val + L.rationalSectionPointCycle := by
  ext x
  exact Int.cast_add _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
