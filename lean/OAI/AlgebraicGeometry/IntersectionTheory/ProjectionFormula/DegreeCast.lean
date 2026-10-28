import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Degree Cast -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

/-! Transport of the actual cycle and Chow gradings along an equality
of natural-number codimensions. -/

def cycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q) :
    X.RationalDimensionCycle p ≃ₗ[ℚ] X.RationalDimensionCycle q := by
  subst q
  exact LinearEquiv.refl ℚ _

theorem cycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q)
    (a : X.RationalDimensionCycle p) (C : X.DimensionCycleSupport q) :
    cycle X h a C = a ⟨C.val, C.property.trans h.symm⟩ := by
  subst q
  rfl

theorem cycle_mem_relations (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q)
    (a : X.RationalDimensionCycle p) :
    cycle X h a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q ↔ a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p := by
  subst q
  rfl

def chow (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q) :
    CycleClass.Thom.IntersectionGeometry.ChowQ X p ≃ₗ[ℚ] CycleClass.Thom.IntersectionGeometry.ChowQ X q := by
  subst q
  exact LinearEquiv.refl ℚ _

theorem chow_mk (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q)
    (a : X.RationalDimensionCycle p) :
    chow X h (ProperCycleLinearity.cycleToChowQ X p a) =
      ProperCycleLinearity.cycleToChowQ X q (cycle X h a) := by
  subst q
  rfl

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast.ExteriorCycleLinear

/-! The actual reduced exterior product and the second product projection
pullback are linear on finite cycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

def exteriorMap (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver) (p q : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] Y.RationalDimensionCycle q →ₗ[ℚ]
      Z.RationalDimensionCycle (p + q) :=
  Finsupp.linearCombination ℚ (fun A => Finsupp.linearCombination ℚ
    (fun B => CycleClass.Thom.IntersectionGeometry.reducedClosedCycle Z (p + q) (CycleClass.Thom.IntersectionGeometry.productClosedSupport X Y Z πX πY A.val B.val)))

theorem exteriorMap_apply (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : Y.RationalDimensionCycle q) :
    exteriorMap X Y Z πX πY p q a b = CycleClass.Thom.IntersectionGeometry.exteriorCycleProduct X Y Z πX πY hprod p q a b := by
  simp only [exteriorMap, CycleClass.Thom.IntersectionGeometry.exteriorCycleProduct, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]

def secondPullbackMap {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y) (p : ℕ) :
    Y.RationalDimensionCycle p →ₗ[ℚ] P.space.RationalDimensionCycle p :=
  (cycle P.space (Nat.zero_add p)).toLinearMap.comp
    (exteriorMap X Y P.space P.fst P.snd 0 p (ProperCycleLinearity.fundamentalCycle X))

theorem cycle_cast (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q)
    (a : X.RationalDimensionCycle p) :
    cycle X h a = cast (congrArg X.RationalDimensionCycle h) a := by
  subst q
  rfl

theorem secondPullbackMap_apply {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
    (p : ℕ) (a : Y.RationalDimensionCycle p) :
    secondPullbackMap P p a = P.secondPullbackCycle p a := by
  rw [secondPullbackMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, cycle_cast,
    exteriorMap_apply X Y P.space P.fst P.snd P.isLimit]
  rfl

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast.ExteriorCycleLinear

end

end OAI
