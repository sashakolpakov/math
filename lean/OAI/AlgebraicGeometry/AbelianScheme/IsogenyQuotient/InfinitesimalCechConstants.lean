import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechConstants
import OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseCechCycles

/-! # Infinitesimal Cech Constants -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalCechConstants.Construction

noncomputable section

/-! If an actual infinitesimal fiber has only base functions, the
tensor reduction of the native Cech complex has exactly the constant
zero-cycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

open OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseCechCycles.Construction

universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} [X.IsSeparated]
  (f : X ⟶ Spec (.of R)) {ι : Type u} [LinearOrder ι] [Finite ι]
  (U : ι → X.Opens) (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i)) (n : ℕ)

include ha in
set_option backward.isDefEq.respectTransparency false in
theorem infinitesimalCech_constants_exact
    [IsIso (pullback.snd f (FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).appTop] :
    Function.Exact ((Relative.CechConstants.Construction.relativeCechConstants f U hU).lTensor (R ⧸ I ^ (n + 1)))
      (((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom.lTensor (R ⧸ I ^ (n + 1))) := by
  let D := FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U
  let J := I ^ (n + 1)
  let e0 := TensorProduct.quotTensorEquivQuotSMul (D.X 0) J
  let e1 := TensorProduct.quotTensorEquivQuotSMul (D.X 1) J
  let E := FormalGeometry.Completion.Infinitesimal.CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U ha hU n
  intro x
  constructor
  · intro hx
    have hcomm := ConcreteCategory.congr_hom ((FormalGeometry.Completion.AdicReduction.Construction.adicReductionTensorIso J).hom.naturality (D.d 0 1)) x
    have hy : ((FormalGeometry.Completion.AdicReduction.Construction.adicReductionComplex J D).d 0 1).hom (e0 x) = 0 := by
      change e1 ((D.d 0 1).hom.lTensor (R ⧸ J) x) =
        ((FormalGeometry.Completion.AdicReduction.Construction.adicReductionComplex J D).d 0 1).hom (e0 x) at hcomm
      exact hcomm.symm.trans ((congrArg e1 hx).trans (map_zero e1))
    let y : ((FormalGeometry.Completion.AdicReduction.Construction.adicReductionComplex J D).d 0 1).hom.ker := ⟨e0 x, hy⟩
    have hs : Function.Surjective (FormalGeometry.Completion.FunctionsComparison.Construction.infinitesimalBaseSectionsMap I f n) :=
      (ConcreteCategory.bijective_of_isIso
        ((Scheme.ΓSpecIso (.of (R ⧸ J))).inv ≫ (pullback.snd f (FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).appTop)).surjective
    obtain ⟨rbar, hr⟩ := hs (E.symm y)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective rbar
    have he : e0 x = Submodule.Quotient.mk (Relative.CechConstants.Construction.relativeCechConstants f U hU r) := by
      have h := congrArg (fun z => (E z).val) hr
      rw [E.apply_symm_apply] at h
      exact h.symm.trans (FormalGeometry.Completion.BaseCechCycles.Construction.infinitesimalSectionsZeroCyclesEquiv_base_mk f U hU I ha n r)
    refine ⟨1 ⊗ₜ[R] r, ?_⟩
    apply e0.injective
    simpa [e0] using he.symm
  · rintro ⟨r, rfl⟩
    have hzero : (D.d 0 1).hom.comp (Relative.CechConstants.Construction.relativeCechConstants f U hU) = 0 := by
      apply LinearMap.ext
      intro r
      exact Relative.CechConstants.Construction.relativeCechConstants_cycle f U hU r
    rw [← LinearMap.lTensor_comp_apply, hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalCechConstants.Construction
