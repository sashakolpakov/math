import OAI.AlgebraicGeometry.Cycles.Functoriality.UnitCap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.MapCharacterization
import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import OAI.AlgebraicGeometry.ComplexMultiplication.ClassDescent

/-! # Cycle Operations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CycleOperations.CM.Construction

noncomputable section

/-!
Exact cycle-operation inputs for CMReduction and their consequences for the genuine
rational cycle-class images. The input propositions repeat the native Functoriality,
LineBundleCycles, and ThomClass specifications; no compatibility statement stub is used.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def FunctorialityInput : Prop :=
  ∀ {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X p),
    Y.geometricCycleClassMap q (Cycles.Functoriality.UnitCap.cyclePushforward f hf p q hdeg z) =
      Cycles.Functoriality.UnitCap.cohomologyPushforward f hf p q hdeg (X.geometricCycleClassMap p z)

def LineBundleCyclesInput : Prop :=
  ∀ (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : X.toOver ⟶ Y.toOver) (p : ℕ),
    ∃ (clX : Divisors.LineBundles.Chow.BundleCycles.ChowQ X p ⟶ X.rationalCohomology (p + p))
      (clY : Divisors.LineBundles.Chow.BundleCycles.ChowQ Y p ⟶ Y.rationalCohomology (p + p))
      (pull : Divisors.LineBundles.Chow.BundleCycles.ChowQ Y p ⟶ Divisors.LineBundles.Chow.BundleCycles.ChowQ X p),
      Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles.IsGeometricCycleClass X p clX ∧
      Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles.IsGeometricCycleClass Y p clY ∧
      Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles.IsGeometricGraphPullback f p pull ∧
      (∀ (clX' : Divisors.LineBundles.Chow.BundleCycles.ChowQ X p ⟶ X.rationalCohomology (p + p))
        (clY' : Divisors.LineBundles.Chow.BundleCycles.ChowQ Y p ⟶ Y.rationalCohomology (p + p))
        (pull' : Divisors.LineBundles.Chow.BundleCycles.ChowQ Y p ⟶ Divisors.LineBundles.Chow.BundleCycles.ChowQ X p),
        Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles.IsGeometricCycleClass X p clX' →
        Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles.IsGeometricCycleClass Y p clY' →
        Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles.IsGeometricGraphPullback f p pull' →
        clX' = clX ∧ clY' = clY ∧ pull' = pull) ∧
      ∀ α : Divisors.LineBundles.Chow.BundleCycles.ChowQ Y p,
        clX (pull α) = Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (clY α)

def ExteriorInput : Prop :=
  ∀ (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY))
    (p q : ℕ) (a : X.RationalDimensionCycle p) (b : Y.RationalDimensionCycle q),
    Z.geometricCycleClassMap (p + q)
        (CycleClass.Thom.IntersectionGeometry.exteriorCycleProduct X Y Z πX πY hprod p q a b) =
      cast (congrArg (fun n => (Z.rationalCohomology n : Type))
        (add_add_add_comm p p q q))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ)
          (Betti.Scheme.schemePointSpace Z.toOver) (p + p) (q + q)
          (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) πX
            (X.geometricCycleClassMap p a))
          (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (q + q) πY
            (Y.geometricCycleClassMap q b)))

theorem rational_pushforward_algebraic (h_Functoriality : FunctorialityInput)
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ) (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (a : X.rationalCohomology (p + p))
    (ha : a ∈ X.geometricAlgebraicClasses p) :
    Cycles.Functoriality.UnitCap.cohomologyPushforward f hf p q hdeg a ∈ Y.geometricAlgebraicClasses q := by
  obtain ⟨z, rfl⟩ := ha
  exact ⟨Cycles.Functoriality.UnitCap.cyclePushforward f hf p q hdeg z, h_Functoriality f hf p q hdeg z⟩

theorem rational_pullback_algebraic (h_LineBundleCycles : LineBundleCyclesInput)
    (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : X.toOver ⟶ Y.toOver)
    (p : ℕ) (a : Y.rationalCohomology (p + p))
    (ha : a ∈ Y.geometricAlgebraicClasses p) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f a ∈ X.geometricAlgebraicClasses p := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨clX, clY, pull, hclX, hclY, _, _, hcompat⟩ := h_LineBundleCycles X Y f p
  obtain ⟨w, hw⟩ := Divisors.LineBundles.Chow.BundleCycles.cycleToChowQ_surjective X p (pull (Divisors.LineBundles.Chow.BundleCycles.cycleToChowQ Y p z))
  refine ⟨w, ?_⟩
  rw [← hclX w, hw, hcompat, hclY z]

theorem rational_exterior_product_algebraic (h_ThomClass : ExteriorInput)
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY))
    (p q : ℕ) (a : X.rationalCohomology (p + p)) (b : Y.rationalCohomology (q + q))
    (ha : a ∈ X.geometricAlgebraicClasses p)
    (hb : b ∈ Y.geometricAlgebraicClasses q) :
    cast (congrArg (fun n => (Z.rationalCohomology n : Type))
      (add_add_add_comm p p q q))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ)
        (Betti.Scheme.schemePointSpace Z.toOver) (p + p) (q + q)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) πX a)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (q + q) πY b)) ∈
      Z.geometricAlgebraicClasses (p + q) := by
  obtain ⟨za, rfl⟩ := ha
  obtain ⟨zb, rfl⟩ := hb
  exact ⟨CycleClass.Thom.IntersectionGeometry.exteriorCycleProduct X Y Z πX πY hprod p q za zb,
    h_ThomClass X Y Z πX πY hprod p q za zb⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CycleOperations.CM.Construction
