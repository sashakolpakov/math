import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.CoordinateRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.FunctionFieldUnitGerm
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Divisor

/-! # Rational Coefficient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

section

/-! # LineBundleCycles: actual frame-change identities for rational sections on arbitrary common opens -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionCoordinate_transition (x y : X) (W : X.Opens) [Nonempty W]
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y) :
    L.rationalSectionCoordinate x =
      FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W (L.ambientTransitionOn x y W hx hy) * L.rationalSectionCoordinate y := by
  let V := W ⊓ L.rationalReferenceOpen
  let : Nonempty V := ⟨⟨genericPoint X,
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using ‹Nonempty W›),
    L.mem_trivializingOpen (genericPoint X)⟩⟩
  have hxV : V ≤ L.rationalCoordinateDomain x := fun _ hv => ⟨hx hv.1, hv.2⟩
  have hyV : V ≤ L.rationalCoordinateDomain y := fun _ hv => ⟨hy hv.1, hv.2⟩
  have ht : FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W (L.ambientTransitionOn x y W hx hy) =
      FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm V (L.ambientTransitionOn x y V (inf_le_left.trans hx) (inf_le_left.trans hy)) := by
    rw [← L.ambientTransitionOn_restrict x y (show V ≤ W from inf_le_left) hx hy]
    exact (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_restrict (show V ≤ W from inf_le_left) _).symm
  rw [L.rationalSectionCoordinate_on_open x V hxV, L.rationalSectionCoordinate_on_open y V hyV, ht]
  change FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm V _ = FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm V _ * FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm V _
  rw [← map_mul]
  exact congrArg (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm V)
    (L.ambientTransitionOn_cocycle x y (genericPoint X) V (inf_le_left.trans hx)
      (inf_le_left.trans hy) inf_le_right).symm

variable [AlgebraicGeometry.IsNoetherian X]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionDivisor_local_order (a : X.functionFieldˣ) (x y : X)
    (hy : y ∈ L.trivializingOpen x) :
    L.rationalSectionPointDivisorWithCoefficient a y = X.ord (a.val * (L.rationalSectionCoordinate x).val) y := by
  let W := L.trivializingOpen x ⊓ L.trivializingOpen y
  have hyW : y ∈ W := ⟨hy, L.mem_trivializingOpen y⟩
  let : Nonempty W := ⟨⟨y, hyW⟩⟩
  rw [L.rationalSectionPointDivisorWithCoefficient_apply a y,
    L.rationalSectionCoordinate_transition x y W inf_le_left inf_le_right]
  change X.ord (a.val * (L.rationalSectionCoordinate y).val) y =
    X.ord (a.val * ((FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _).val * (L.rationalSectionCoordinate y).val)) y
  rw [Scheme.ord_mul a.ne_zero (L.rationalSectionCoordinate_ne_zero y),
    Scheme.ord_mul a.ne_zero (mul_ne_zero (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _).ne_zero (L.rationalSectionCoordinate_ne_zero y)),
    Scheme.ord_mul (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _).ne_zero (L.rationalSectionCoordinate_ne_zero y),
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_order W _ y hyW, zero_add]

end

section

/-! # LineBundleCycles: an actual local section has a frame-independent coefficient in the generic rational line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient (x : X) (U : X.Opens) [Nonempty U]
    (hU : U ≤ L.trivializingOpen x) (s : Γ(L.sheaf, U)) : X.functionField :=
  X.germToFunctionField U (L.sectionFrame x U hU s) / (L.rationalSectionCoordinate x).val

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient_injective (x : X) (U : X.Opens) [Nonempty U]
    (hU : U ≤ L.trivializingOpen x) : Function.Injective (L.localRationalCoefficient x U hU) := by
  intro s t h
  apply (L.sectionFrame x U hU).injective
  apply X.germToFunctionField_injective U
  exact (div_left_inj' (L.rationalSectionCoordinate x).ne_zero).mp h

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient_frame (x y : X) (U : X.Opens) [Nonempty U]
    (hx : U ≤ L.trivializingOpen x) (hy : U ≤ L.trivializingOpen y) (s : Γ(L.sheaf, U)) :
    L.localRationalCoefficient x U hx s = L.localRationalCoefficient y U hy s := by
  have ht : L.sectionFrame x U hx s = (L.ambientTransitionOn x y U hx hy).val * L.sectionFrame y U hy s :=
    LineBundle.FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_coordinates _ _ _
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient
  rw [ht, map_mul, L.rationalSectionCoordinate_transition x y U hx hy]
  change (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm U (L.ambientTransitionOn x y U hx hy)).val *
      X.germToFunctionField U (L.sectionFrame y U hy s) /
      ((FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm U (L.ambientTransitionOn x y U hx hy)).val * (L.rationalSectionCoordinate y).val) = _
  exact mul_div_mul_left _ _ (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm U _).ne_zero

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient_restrict (x : X) {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) (hU : U ≤ L.trivializingOpen x) (s : Γ(L.sheaf, U)) :
    L.localRationalCoefficient x V (hVU.trans hU) (L.sheaf.presheaf.map (homOfLE hVU).op s) =
      L.localRationalCoefficient x U hU s := by
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient
  rw [L.sectionFrame_naturality x hVU hU]
  rw [RationalBoundary.BundleCycles.RationalUnitRepresentative.germ_restrict hVU]

end

/-! # LineBundleCycles: the actual generic rational coefficient of a section on any nonempty open subset -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericCoefficientDomain (U : X.Opens) : X.Opens := U ⊓ L.rationalReferenceOpen

instance Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericCoefficientDomain_nonempty (U : X.Opens) [Nonempty U] :
    Nonempty (L.genericCoefficientDomain U) :=
  ⟨⟨genericPoint X,
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›),
    L.mem_trivializingOpen (genericPoint X)⟩⟩

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient (U : X.Opens) [Nonempty U] (s : Γ(L.sheaf, U)) : X.functionField :=
  L.localRationalCoefficient (genericPoint X) (L.genericCoefficientDomain U) inf_le_right
    (L.sheaf.presheaf.map (homOfLE (show L.genericCoefficientDomain U ≤ U from inf_le_left)).op s)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_eq_local (x : X) (U : X.Opens) [Nonempty U]
    (hU : U ≤ L.trivializingOpen x) (s : Γ(L.sheaf, U)) :
    L.genericSectionCoefficient U s = L.localRationalCoefficient x U hU s := by
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient
  rw [← L.localRationalCoefficient_frame x (genericPoint X) (L.genericCoefficientDomain U)
    (inf_le_left.trans hU) inf_le_right]
  exact L.localRationalCoefficient_restrict x (show L.genericCoefficientDomain U ≤ U from inf_le_left) hU s

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) (s : Γ(L.sheaf, U)) :
    L.genericSectionCoefficient V (L.sheaf.presheaf.map (homOfLE hVU).op s) =
      L.genericSectionCoefficient U s := by
  have hD : L.genericCoefficientDomain V ≤ L.genericCoefficientDomain U := inf_le_inf_right _ hVU
  have h := L.localRationalCoefficient_restrict (genericPoint X) hD inf_le_right
    (L.sheaf.presheaf.map (homOfLE (show L.genericCoefficientDomain U ≤ U from inf_le_left)).op s)
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient
  rw [← ConcreteCategory.comp_apply, ← L.sheaf.presheaf.map_comp] at h ⊢
  exact h

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_injective (U : X.Opens) [Nonempty U] :
    Function.Injective (L.genericSectionCoefficient U) := by
  intro s t h
  apply L.sheaf.isSheaf.section_ext
  intro x hx
  let V : X.Opens := U ⊓ L.trivializingOpen x
  have hxV : x ∈ V := ⟨hx, L.mem_trivializingOpen x⟩
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  refine ⟨V, inf_le_left, hxV, ?_⟩
  apply L.localRationalCoefficient_injective x V inf_le_right
  rw [← L.genericSectionCoefficient_eq_local x V inf_le_right,
    ← L.genericSectionCoefficient_eq_local x V inf_le_right,
    L.genericSectionCoefficient_restrict inf_le_left,
    L.genericSectionCoefficient_restrict inf_le_left]
  exact h

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_zero (U : X.Opens) [Nonempty U] :
    L.genericSectionCoefficient U 0 = 0 := by
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient
  rw [map_zero, map_zero, map_zero, zero_div]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_ne_zero (U : X.Opens) [Nonempty U]
    (s : Γ(L.sheaf, U)) (hs : s ≠ 0) : L.genericSectionCoefficient U s ≠ 0 := by
  intro h
  exact hs (L.genericSectionCoefficient_injective U (h.trans (L.genericSectionCoefficient_zero U).symm))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
