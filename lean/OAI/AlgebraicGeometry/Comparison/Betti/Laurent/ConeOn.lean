import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ConeCoordinates
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! # Cone On -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ConeOn.Dolbeault

noncomputable section

section

/-! The coordinate cone maps are holomorphic on their actual domains. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem laurentConeRatios_differentiableOn (s : Finset ι) (i : ι) (hi : i ∈ s) :
    DifferentiableOn ℂ (ConeCoordinates.Dolbeault.laurentConeRatios i) (SectorTo.Dolbeault.laurentCoordinateDomain s) := by
  apply differentiableOn_pi.mpr
  intro j x hx
  change DifferentiableWithinAt ℂ (fun x : ι → ℂ => x j.val / x i) _ x
  simp only [div_eq_mul_inv]
  exact ((differentiableAt_apply (𝕜 := ℂ) j.val x).fun_mul
    ((differentiableAt_apply (𝕜 := ℂ) i x).fun_inv
      ((SectorTo.Dolbeault.mem_laurentCoordinateDomain s x).mp hx i hi))).differentiableWithinAt

theorem laurentConeAffineLift_differentiable (i : ι) :
    Differentiable ℂ (ConeCoordinates.Dolbeault.laurentConeAffineLift i) := by
  exact (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm.differentiable.comp
    (differentiable_id.prodMk (differentiable_const 1))

theorem laurentConeWeight_differentiableOn (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    DifferentiableOn ℂ (fun x : ι → ℂ => x i ^ d) (SectorTo.Dolbeault.laurentCoordinateDomain s) := by
  intro x hx
  exact ((differentiableAt_apply (𝕜 := ℂ) i x).zpow
    (Or.inl ((SectorTo.Dolbeault.mem_laurentCoordinateDomain s x).mp hx i hi))).differentiableWithinAt

end

section

/-! Holomorphic lift and descent between an affine chart and its coordinate cone. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentConeLiftSection (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ConeCoordinates.Dolbeault.laurentAffineDomain s i)) :
    Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s) :=
  PolynomialHolomorphicSections.AnalyticLocal.functionSectionOfDifferentiable _
    (fun x => x i ^ d * FiberVanishing.Dolbeault.holomorphicFunctionExtension _ f (ConeCoordinates.Dolbeault.laurentConeRatios i x))
    ((laurentConeWeight_differentiableOn s i hi d).fun_mul
      ((FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ f).comp
        (laurentConeRatios_differentiableOn s i hi) (ConeCoordinates.Dolbeault.laurentConeRatios_mapsTo s i hi)))

theorem laurentConeLiftSection_apply (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ConeCoordinates.Dolbeault.laurentAffineDomain s i)) (x : SectorTo.Dolbeault.laurentCoordinateDomain s) :
    (laurentConeLiftSection s i hi d f).val x = x.val i ^ d * f.val (ConeCoordinates.Dolbeault.laurentConeNormalize s i hi x) :=
  congrArg (x.val i ^ d * ·) (Holomorphic.CoefficientMem.openCoefficientExtension_apply _ f.val (ConeCoordinates.Dolbeault.laurentConeNormalize s i hi x))

def laurentConeDescendSection (s : Finset ι) (i : ι)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s)) :
    Holomorphic.FunctionPure.holomorphicFunctions (ConeCoordinates.Dolbeault.laurentAffineDomain s i) :=
  PolynomialHolomorphicSections.AnalyticLocal.functionSectionOfDifferentiable _
    (fun z => FiberVanishing.Dolbeault.holomorphicFunctionExtension _ f (ConeCoordinates.Dolbeault.laurentConeAffineLift i z))
    ((FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ f).comp
      (laurentConeAffineLift_differentiable i).differentiableOn (ConeCoordinates.Dolbeault.laurentConeAffineLift_mapsTo s i))

theorem laurentConeDescendSection_apply (s : Finset ι) (i : ι)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s)) (z : ConeCoordinates.Dolbeault.laurentAffineDomain s i) :
    (laurentConeDescendSection s i f).val z = f.val (ConeCoordinates.Dolbeault.laurentConeAffinePoint s i z) :=
  Holomorphic.CoefficientMem.openCoefficientExtension_apply _ f.val (ConeCoordinates.Dolbeault.laurentConeAffinePoint s i z)

def laurentConeLiftSectionMap (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    Holomorphic.FunctionPure.holomorphicFunctions (ConeCoordinates.Dolbeault.laurentAffineDomain s i) →ₗ[ℂ] Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s) where
  toFun := laurentConeLiftSection s i hi d
  map_add' f g := by
    apply Subtype.ext
    funext x
    change (laurentConeLiftSection s i hi d (f + g)).val x =
      (laurentConeLiftSection s i hi d f).val x + (laurentConeLiftSection s i hi d g).val x
    rw [laurentConeLiftSection_apply, laurentConeLiftSection_apply, laurentConeLiftSection_apply]
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change (laurentConeLiftSection s i hi d (c • f)).val x = c * (laurentConeLiftSection s i hi d f).val x
    rw [laurentConeLiftSection_apply, laurentConeLiftSection_apply]
    change x.val i ^ d * (c * f.val _) = c * (x.val i ^ d * f.val _)
    ring

def laurentConeDescendSectionMap (s : Finset ι) (i : ι) :
    Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s) →ₗ[ℂ] Holomorphic.FunctionPure.holomorphicFunctions (ConeCoordinates.Dolbeault.laurentAffineDomain s i) where
  toFun := laurentConeDescendSection s i
  map_add' f g := by
    apply Subtype.ext
    funext x
    change (laurentConeDescendSection s i (f + g)).val x =
      (laurentConeDescendSection s i f).val x + (laurentConeDescendSection s i g).val x
    rw [laurentConeDescendSection_apply, laurentConeDescendSection_apply, laurentConeDescendSection_apply]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change (laurentConeDescendSection s i (c • f)).val x = c * (laurentConeDescendSection s i f).val x
    rw [laurentConeDescendSection_apply, laurentConeDescendSection_apply]
    rfl

end

/-! The normalized affine chart is equivalent to homogeneous cone sections. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem laurentConeRatios_scale (i : ι) (c : ℂ) (hc : c ≠ 0) (x : ι → ℂ) :
    ConeCoordinates.Dolbeault.laurentConeRatios i (FiniteUniqueness.Dolbeault.laurentUniformScale c x) = ConeCoordinates.Dolbeault.laurentConeRatios i x := by
  funext j
  exact mul_div_mul_left (x j.val) (x i) hc

theorem laurentConeNormalize_scaledPoint (s : Finset ι) (i : ι) (hi : i ∈ s)
    (c : ℂ) (hc : c ≠ 0) (x : SectorTo.Dolbeault.laurentCoordinateDomain s) :
    ConeCoordinates.Dolbeault.laurentConeNormalize s i hi (HomogeneousLaurent.Dolbeault.laurentScaledPoint s c hc x) = ConeCoordinates.Dolbeault.laurentConeNormalize s i hi x :=
  Subtype.ext (laurentConeRatios_scale i c hc x.val)

theorem laurentConeLiftSection_homogeneous (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ConeCoordinates.Dolbeault.laurentAffineDomain s i)) :
    laurentConeLiftSectionMap s i hi d f ∈ HomogeneousLaurent.Dolbeault.laurentHomogeneousSections s d := by
  intro c hc x
  change (laurentConeLiftSection s i hi d f).val (HomogeneousLaurent.Dolbeault.laurentScaledPoint s c hc x) =
    c ^ d * (laurentConeLiftSection s i hi d f).val x
  rw [laurentConeLiftSection_apply, laurentConeLiftSection_apply, laurentConeNormalize_scaledPoint]
  change (c * x.val i) ^ d * f.val _ = c ^ d * (x.val i ^ d * f.val _)
  rw [mul_zpow, mul_assoc]

theorem laurentConeDescend_lift (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ConeCoordinates.Dolbeault.laurentAffineDomain s i)) :
    laurentConeDescendSectionMap s i (laurentConeLiftSectionMap s i hi d f) = f := by
  apply Subtype.ext
  funext z
  change (laurentConeDescendSection s i (laurentConeLiftSection s i hi d f)).val z = f.val z
  rw [laurentConeDescendSection_apply, laurentConeLiftSection_apply, ConeCoordinates.Dolbeault.laurentConeNormalize_affinePoint]
  change ConeCoordinates.Dolbeault.laurentConeAffineLift i z.val i ^ d * f.val z = f.val z
  rw [ConeCoordinates.Dolbeault.laurentConeAffineLift_same, one_zpow, one_mul]

theorem laurentConeLift_descend (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s)) (hf : f ∈ HomogeneousLaurent.Dolbeault.laurentHomogeneousSections s d) :
    laurentConeLiftSectionMap s i hi d (laurentConeDescendSectionMap s i f) = f := by
  apply Subtype.ext
  funext x
  change (laurentConeLiftSection s i hi d (laurentConeDescendSection s i f)).val x = f.val x
  rw [laurentConeLiftSection_apply, laurentConeDescendSection_apply]
  have hxi : x.val i ≠ 0 := (SectorTo.Dolbeault.mem_laurentCoordinateDomain s x.val).mp x.property i hi
  have hp : ConeCoordinates.Dolbeault.laurentConeAffinePoint s i (ConeCoordinates.Dolbeault.laurentConeNormalize s i hi x) =
      HomogeneousLaurent.Dolbeault.laurentScaledPoint s (x.val i)⁻¹ (inv_ne_zero hxi) x :=
    Subtype.ext (ConeCoordinates.Dolbeault.laurentConeAffinePoint_normalize s i hi x)
  rw [hp, hf (x.val i)⁻¹ (inv_ne_zero hxi) x, inv_zpow, ← mul_assoc,
    mul_inv_cancel₀ (zpow_ne_zero d hxi), one_mul]

def laurentConeSectionEquiv (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    Holomorphic.FunctionPure.holomorphicFunctions (ConeCoordinates.Dolbeault.laurentAffineDomain s i) ≃ₗ[ℂ] HomogeneousLaurent.Dolbeault.laurentHomogeneousSections s d where
  toFun f := ⟨laurentConeLiftSectionMap s i hi d f, laurentConeLiftSection_homogeneous s i hi d f⟩
  invFun f := laurentConeDescendSectionMap s i f.val
  map_add' f g := Subtype.ext ((laurentConeLiftSectionMap s i hi d).map_add f g)
  map_smul' c f := Subtype.ext ((laurentConeLiftSectionMap s i hi d).map_smul c f)
  left_inv := laurentConeDescend_lift s i hi d
  right_inv f := Subtype.ext (laurentConeLift_descend s i hi d f.val f.property)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ConeOn.Dolbeault
