import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FrameComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # Rational Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: rational-section coordinates of an actual line bundle on an integral scheme

The generator on the chart of the generic point determines a rational section.
Its coordinates in every other chart are germs of actual transition units.
Their orders of vanishing vanish on the reference chart.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
variable [IsIntegral X]

/-- Every nonempty trivializing chart contains the generic point. -/
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericPoint_mem_trivializingOpen (x : X) :
    genericPoint X ∈ L.trivializingOpen x := by
  apply ((genericPoint_spec X).mem_open_set_iff (L.trivializingOpen x).isOpen).mpr
  exact ⟨x, Set.mem_univ x, L.mem_trivializingOpen x⟩

/-- The chart whose generator is used as the reference rational section. -/
abbrev Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalReferenceOpen : X.Opens :=
  L.trivializingOpen (genericPoint X)

/-- The nonempty overlap on which a rational-section coordinate is a regular unit. -/
abbrev Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalCoordinateDomain (x : X) : X.Opens :=
  L.trivializingOpen x ⊓ L.rationalReferenceOpen

instance Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalCoordinateDomain_nonempty (x : X) :
    Nonempty (L.rationalCoordinateDomain x) :=
  ⟨⟨genericPoint X, L.genericPoint_mem_trivializingOpen x,
    L.mem_trivializingOpen (genericPoint X)⟩⟩

/-- The rational coordinate of the reference generator in the frame at `x`.
It is a unit in the actual function field, obtained from a genuine regular transition. -/
def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionCoordinate (x : X) : X.functionFieldˣ :=
  Units.map (X.germToFunctionField (L.rationalCoordinateDomain x)).hom.toMonoidHom
    (L.ambientTransitionOn x (genericPoint X) (L.rationalCoordinateDomain x)
      inf_le_left inf_le_right)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionCoordinate_ne_zero (x : X) :
    (L.rationalSectionCoordinate x : X.functionField) ≠ 0 :=
  Units.ne_zero _

variable [IsLocallyNoetherian X]

/-- The local-length order of the rational section in the chart at the point. -/
def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionOrder (x : X) : ℤ :=
  X.ord (L.rationalSectionCoordinate x : X.functionField) x

/-- The reference section is a generator on its original trivializing chart. -/
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionOrder_zero_on_reference (x : X)
    (hx : x ∈ L.rationalReferenceOpen) : L.rationalSectionOrder x = 0 := by
  change X.ord
    (X.germToFunctionField (L.rationalCoordinateDomain x)
      (L.ambientTransitionOn x (genericPoint X) (L.rationalCoordinateDomain x)
        inf_le_left inf_le_right : Γ(X, L.rationalCoordinateDomain x))) x = 0
  exact Scheme.ord_of_isUnit (Units.isUnit _) ⟨L.mem_trivializingOpen x, hx⟩

/-- Only actual codimension-one points can carry a nonzero multiplicity. -/
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionOrder_eq_zero_of_coheight_ne_one (x : X)
    (hx : Order.coheight x ≠ 1) : L.rationalSectionOrder x = 0 :=
  Scheme.ord_eq_zero_of_coheight_neq_one hx _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
