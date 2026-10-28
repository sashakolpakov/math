import OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicReduction

/-! # Cochain Reduced Kernels -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainReducedKernels.Construction

noncomputable section

/-! Compatible reduced zero-cycles are invariant under a cochain map
which is a degree-zero quasi-isomorphism at every actual ideal-power reduction. -/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R]
  {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)

/-- The actual degree-zero component restricted to differential kernels. -/
def cochainKernelMap : (C.d 0 1).hom.ker →ₗ[R] (D.d 0 1).hom.ker where
  toFun x := ⟨φ.f 0 x.val, by
    change (φ.f 0 ≫ D.d 0 1) x.val = 0
    rw [φ.comm]
    change φ.f 1 (C.d 0 1 x.val) = 0
    rw [x.property, map_zero]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem cochainKernelMap_bijective [QuasiIsoAt φ 0] :
    Function.Bijective (cochainKernelMap φ) := by
  have he : cochainKernelMap φ = (Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv φ).toLinearMap := by
    ext x
    exact (Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val φ x).symm
  rw [he]
  exact (Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv φ).bijective

variable (I : Ideal R)

/-- The actual quotient transition sends reduced cycles to reduced cycles. -/
def reducedCycleTransition (C : CochainComplex (ModuleCat.{u} R) ℕ)
    {m n : ℕ} (h : m ≤ n) :
    ((AdicReduction.Construction.adicReductionComplex (I ^ n) C).d 0 1).hom.ker →ₗ[R]
      ((AdicReduction.Construction.adicReductionComplex (I ^ m) C).d 0 1).hom.ker where
  toFun x := ⟨AdicCompletion.transitionMap I (C.X 0) h x.val, by
    change (C.d 0 1).hom.reduceModIdeal (I ^ m)
      (AdicCompletion.transitionMap I (C.X 0) h x.val) = 0
    have hc := LinearMap.congr_fun
      (AdicCompletion.transitionMap_comp_reduceModIdeal I (C.d 0 1).hom h) x.val
    calc
      _ = AdicCompletion.transitionMap I (C.X 1) h
          ((C.d 0 1).hom.reduceModIdeal (I ^ n) x.val) := hc.symm
      _ = 0 := by
        have hx : (C.d 0 1).hom.reduceModIdeal (I ^ n) x.val = 0 := x.property
        rw [hx, map_zero]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem reducedCycleTransition_naturality {m n : ℕ} (h : m ≤ n)
    (x : ((AdicReduction.Construction.adicReductionComplex (I ^ n) C).d 0 1).hom.ker) :
    cochainKernelMap (AdicReduction.Construction.adicReductionMap (I ^ m) φ) (reducedCycleTransition I C h x) =
      reducedCycleTransition I D h (cochainKernelMap (AdicReduction.Construction.adicReductionMap (I ^ n) φ) x) := by
  apply Subtype.ext
  exact (LinearMap.congr_fun
    (AdicCompletion.transitionMap_comp_reduceModIdeal I (φ.f 0).hom h) x.val).symm

/-- The original cochain map acts coordinatewise on compatible reduced cycles. -/
def compatibleReducedCochainMap :
    CompatibleReducedKernels.Construction.compatibleReducedKernels I (C.d 0 1).hom →ₗ[R]
      CompatibleReducedKernels.Construction.compatibleReducedKernels I (D.d 0 1).hom where
  toFun x := ⟨fun n => (φ.f 0).hom.reduceModIdeal (I ^ n) (x.val n),
    (fun h => by
      have hc := LinearMap.congr_fun
        (AdicCompletion.transitionMap_comp_reduceModIdeal I (φ.f 0).hom h) (x.val _)
      exact hc.trans (congrArg ((φ.f 0).hom.reduceModIdeal _) (x.property.1 h))),
    fun n => (cochainKernelMap (AdicReduction.Construction.adicReductionMap (I ^ n) φ)
      ⟨x.val n, x.property.2 n⟩).property⟩
  map_add' _ _ := by apply Subtype.ext; funext n; exact map_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact ((φ.f 0).hom.reduceModIdeal (I ^ n)).restrictScalars R |>.map_smul r (x.val n)

theorem compatibleReducedCochainMap_bijective
    [∀ n, QuasiIsoAt (AdicReduction.Construction.adicReductionMap (I ^ n) φ) 0] :
    Function.Bijective (compatibleReducedCochainMap φ I) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext n
    exact congrArg Subtype.val ((cochainKernelMap_bijective
      (AdicReduction.Construction.adicReductionMap (I ^ n) φ)).injective
      (a₁ := ⟨x.val n, x.property.2 n⟩) (a₂ := ⟨y.val n, y.property.2 n⟩)
      (Subtype.ext (congrArg (fun z : CompatibleReducedKernels.Construction.compatibleReducedKernels I (D.d 0 1).hom => z.val n) hxy)))
  · intro x
    let e (n : ℕ) := Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv (AdicReduction.Construction.adicReductionMap (I ^ n) φ)
    let y (n : ℕ) := (e n).symm ⟨x.val n, x.property.2 n⟩
    have hy (n : ℕ) : cochainKernelMap (AdicReduction.Construction.adicReductionMap (I ^ n) φ) (y n) =
        ⟨x.val n, x.property.2 n⟩ := by
      apply Subtype.ext
      change (AdicReduction.Construction.adicReductionMap (I ^ n) φ).f 0 (y n).val = x.val n
      rw [← Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val]
      exact congrArg Subtype.val ((e n).apply_symm_apply _)
    have hc {m n : ℕ} (h : m ≤ n) :
        AdicCompletion.transitionMap I (C.X 0) h (y n).val = (y m).val := by
      change (reducedCycleTransition I C h (y n)).val = (y m).val
      apply congrArg Subtype.val
      apply (cochainKernelMap_bijective (AdicReduction.Construction.adicReductionMap (I ^ m) φ)).injective
      rw [reducedCycleTransition_naturality, hy, hy]
      exact Subtype.ext (x.property.1 h)
    refine ⟨⟨fun n => (y n).val, fun h => hc h, fun n => (y n).property⟩, ?_⟩
    apply Subtype.ext
    funext n
    exact congrArg Subtype.val (hy n)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainReducedKernels.Construction
