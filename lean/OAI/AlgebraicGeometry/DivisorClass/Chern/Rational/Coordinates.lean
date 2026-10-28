import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-!
# ChernClass: rational-section coordinates of an actual line bundle on an integral scheme

The generator on the chart of the generic point determines a rational section.
Its coordinates in every other chart are germs of actual transition units.
Their orders of vanishing vanish on the reference chart.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

/-- Every nonempty trivializing chart contains the generic point. -/
theorem Line.Bundles.AlgebraicLineBundle.genericPoint_mem_trivializingOpen (x : X.carrier) :
    genericPoint X.carrier ∈ L.trivializingOpen x := by
  apply ((genericPoint_spec X.carrier).mem_open_set_iff (L.trivializingOpen x).isOpen).mpr
  exact ⟨x, Set.mem_univ x, L.mem_trivializingOpen x⟩

/-- The chart whose generator is used as the reference rational section. -/
abbrev Line.Bundles.AlgebraicLineBundle.rationalReferenceOpen : X.carrier.Opens :=
  L.trivializingOpen (genericPoint X.carrier)

/-- The nonempty overlap on which a rational-section coordinate is a regular unit. -/
abbrev Line.Bundles.AlgebraicLineBundle.rationalCoordinateDomain (x : X.carrier) : X.carrier.Opens :=
  L.trivializingOpen x ⊓ L.rationalReferenceOpen

instance Line.Bundles.AlgebraicLineBundle.rationalCoordinateDomain_nonempty (x : X.carrier) :
    Nonempty (L.rationalCoordinateDomain x) :=
  ⟨⟨genericPoint X.carrier, L.genericPoint_mem_trivializingOpen x,
    L.mem_trivializingOpen (genericPoint X.carrier)⟩⟩

/-- The rational coordinate of the reference generator in the frame at `x`.
It is a unit in the actual function field, obtained from a genuine regular transition. -/
def Line.Bundles.AlgebraicLineBundle.rationalSectionCoordinate (x : X.carrier) : X.carrier.functionFieldˣ :=
  Units.map (X.carrier.germToFunctionField (L.rationalCoordinateDomain x)).hom.toMonoidHom
    (L.ambientTransitionOn x (genericPoint X.carrier) (L.rationalCoordinateDomain x)
      inf_le_left inf_le_right)

theorem Line.Bundles.AlgebraicLineBundle.rationalSectionCoordinate_ne_zero (x : X.carrier) :
    (L.rationalSectionCoordinate x : X.carrier.functionField) ≠ 0 :=
  Units.ne_zero _

/-- The local-length order of the rational section in the chart at the point. -/
def Line.Bundles.AlgebraicLineBundle.rationalSectionOrder (x : X.carrier) : ℤ :=
  X.carrier.ord (L.rationalSectionCoordinate x : X.carrier.functionField) x

/-- The reference section is a generator on its original trivializing chart. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionOrder_zero_on_reference (x : X.carrier)
    (hx : x ∈ L.rationalReferenceOpen) : L.rationalSectionOrder x = 0 := by
  change X.carrier.ord
    (X.carrier.germToFunctionField (L.rationalCoordinateDomain x)
      (L.ambientTransitionOn x (genericPoint X.carrier) (L.rationalCoordinateDomain x)
        inf_le_left inf_le_right : Γ(X.carrier, L.rationalCoordinateDomain x))) x = 0
  exact Scheme.ord_of_isUnit (Units.isUnit _) ⟨L.mem_trivializingOpen x, hx⟩

/-- Only actual codimension-one points can carry a nonzero multiplicity. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionOrder_eq_zero_of_coheight_ne_one (x : X.carrier)
    (hx : Order.coheight x ≠ 1) : L.rationalSectionOrder x = 0 :=
  Scheme.ord_eq_zero_of_coheight_neq_one hx _

end

/-!
# ChernClass: compatibility of the rational section's local coordinates

Taking the germ at the generic point commutes with restricting the actual
transition units. The cocycle law then gives the usual coordinate-change law.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Rational.Coordinates.Construction

theorem germToFunctionField_restrict (X : Scheme) [IsIntegral X]
    {V U : X.Opens} [Nonempty V] [Nonempty U] (h : V ≤ U) (s : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op s) = X.germToFunctionField U s :=
  X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) _ s

end Rational.Coordinates.Construction

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

/-- The actual transition unit viewed in the function field. -/
def Line.Bundles.AlgebraicLineBundle.genericTransitionUnit (i j : X.carrier) (U : X.carrier.Opens) [Nonempty U]
    (hi : U ≤ L.trivializingOpen i) (hj : U ≤ L.trivializingOpen j) : X.carrier.functionFieldˣ :=
  Units.map (X.carrier.germToFunctionField U).hom.toMonoidHom (L.ambientTransitionOn i j U hi hj)

/-- Further restriction does not change the generic germ of a transition. -/
theorem Line.Bundles.AlgebraicLineBundle.genericTransitionUnit_restrict (i j : X.carrier) {V U : X.carrier.Opens}
    [Nonempty V] [Nonempty U] (h : V ≤ U)
    (hi : U ≤ L.trivializingOpen i) (hj : U ≤ L.trivializingOpen j) :
    L.genericTransitionUnit i j V (h.trans hi) (h.trans hj) = L.genericTransitionUnit i j U hi hj := by
  apply Units.ext
  have hu := congrArg Units.val (L.ambientTransitionOn_restrict i j h hi hj)
  change X.carrier.presheaf.map (homOfLE h).op (L.ambientTransitionOn i j U hi hj : Γ(X.carrier, U)) =
    (L.ambientTransitionOn i j V (h.trans hi) (h.trans hj) : Γ(X.carrier, V)) at hu
  change X.carrier.germToFunctionField V _ = X.carrier.germToFunctionField U _
  rw [← hu]
  exact Rational.Coordinates.Construction.germToFunctionField_restrict X.carrier h _

theorem Line.Bundles.AlgebraicLineBundle.genericTransitionUnit_cocycle (i j k : X.carrier) (U : X.carrier.Opens) [Nonempty U]
    (hi : U ≤ L.trivializingOpen i) (hj : U ≤ L.trivializingOpen j)
    (hk : U ≤ L.trivializingOpen k) :
    L.genericTransitionUnit i j U hi hj * L.genericTransitionUnit j k U hj hk =
      L.genericTransitionUnit i k U hi hk := by
  unfold Line.Bundles.AlgebraicLineBundle.genericTransitionUnit
  rw [← map_mul, L.ambientTransitionOn_cocycle]

/-- A rational section has the usual change-of-coordinate law on every common nonempty open. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionCoordinate_change (i j : X.carrier) (U : X.carrier.Opens) [Nonempty U]
    (hi : U ≤ L.trivializingOpen i) (hj : U ≤ L.trivializingOpen j) :
    L.rationalSectionCoordinate i = L.genericTransitionUnit i j U hi hj * L.rationalSectionCoordinate j := by
  let W := U ⊓ L.rationalReferenceOpen
  have hpU : genericPoint X.carrier ∈ U :=
    ((genericPoint_spec X.carrier).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  let : Nonempty W := ⟨⟨genericPoint X.carrier, hpU, L.mem_trivializingOpen _⟩⟩
  have hWU : W ≤ U := inf_le_left
  have hWi : W ≤ L.rationalCoordinateDomain i := le_inf (hWU.trans hi) inf_le_right
  have hWj : W ≤ L.rationalCoordinateDomain j := le_inf (hWU.trans hj) inf_le_right
  have hci : L.genericTransitionUnit i (genericPoint X.carrier) W
      (hWU.trans hi) inf_le_right = L.rationalSectionCoordinate i :=
    L.genericTransitionUnit_restrict i (genericPoint X.carrier) hWi inf_le_left inf_le_right
  have hcj : L.genericTransitionUnit j (genericPoint X.carrier) W
      (hWU.trans hj) inf_le_right = L.rationalSectionCoordinate j :=
    L.genericTransitionUnit_restrict j (genericPoint X.carrier) hWj inf_le_left inf_le_right
  rw [← hci, ← hcj, ← L.genericTransitionUnit_restrict i j hWU hi hj]
  exact (L.genericTransitionUnit_cocycle i j (genericPoint X.carrier) W
    (hWU.trans hi) (hWU.trans hj) inf_le_right).symm

/-- The divisor multiplicity can be computed in any trivializing chart
containing the point, because changes of frame have order zero there. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionOrder_in_chart (x i : X.carrier)
    (hx : x ∈ L.trivializingOpen i) :
    L.rationalSectionOrder x = X.carrier.ord
      (L.rationalSectionCoordinate i : X.carrier.functionField) x := by
  let U := L.trivializingOpen x ⊓ L.trivializingOpen i
  let : Nonempty U := ⟨⟨x, L.mem_trivializingOpen x, hx⟩⟩
  have hc := congrArg Units.val (L.rationalSectionCoordinate_change x i U inf_le_left inf_le_right)
  change (L.rationalSectionCoordinate x : X.carrier.functionField) =
    (L.genericTransitionUnit x i U inf_le_left inf_le_right : X.carrier.functionField) *
      (L.rationalSectionCoordinate i : X.carrier.functionField) at hc
  unfold Line.Bundles.AlgebraicLineBundle.rationalSectionOrder
  rw [hc, Scheme.ord_mul (Units.ne_zero _) (Units.ne_zero _)]
  have hz : X.carrier.ord
      (L.genericTransitionUnit x i U inf_le_left inf_le_right : X.carrier.functionField) x = 0 := by
    exact Scheme.ord_of_isUnit (Units.isUnit (L.ambientTransitionOn x i U inf_le_left inf_le_right))
      ⟨L.mem_trivializingOpen x, hx⟩
  rw [hz, zero_add]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
