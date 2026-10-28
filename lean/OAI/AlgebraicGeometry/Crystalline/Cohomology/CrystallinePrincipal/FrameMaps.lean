import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PrincipalForms

/-! # Frame Maps -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.FrameMaps.CrystallinePrincipalFrameMaps

noncomputable section

/-!
# Ambient-ring linearity of native frame restrictions

Every inclusion between principal opens of a fixed crystalline object
acts linearly over its original ambient ring. After restricting scalars
to Witt vectors, the maps are exactly the native frame-resolution maps.
-/

open _root_.CategoryTheory Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

local notation "W" => WittVector p k
local notation "QR" => Q.thickening.ring
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B

abbrev Ring (r : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR) : Type u :=
  DividedPowerAlgebra (Localization.Away r.val) (σ →₀ Localization.Away r.val)

variable {r s : PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring} (f : r ⟶ s)

def ringMap : Ring p k B σ Q s →ₐ[QR] Ring p k B σ Q r where
  __ := (CrystallineFrame.Map.CrystallineFrameMap.ambientMap a (Functor.CrystallinePrincipalFunctor.map p k X Q f)).toRingHom
  commutes' x := by
    have h := CrystallineFrame.Map.CrystallineFrameMap.ambientMap_coefficient a
      (Functor.CrystallinePrincipalFunctor.map p k X Q f) (algebraMap QR (Localization.Away s.val) x)
    exact (congrArg (CrystallineFrame.Map.CrystallineFrameMap.ambientMap a (Functor.CrystallinePrincipalFunctor.map p k X Q f))
      (IsScalarTower.algebraMap_apply QR (Localization.Away s.val) (Ring p k B σ Q s) x)).trans
        (h.trans ((congrArg (algebraMap (Localization.Away r.val) (Ring p k B σ Q r))
          (Functor.CrystallinePrincipalFunctor.map_algebraMap p k X Q f x)).trans
            (IsScalarTower.algebraMap_apply QR (Localization.Away r.val) (Ring p k B σ Q r) x).symm))

def moduleMap (n : ℕ) :
    Koszul.Tensor.KoszulTensor.Term W σ (Ring p k B σ Q s) n →ₗ[QR]
      Koszul.Tensor.KoszulTensor.Term W σ (Ring p k B σ Q r) n :=
  TensorProduct.AlgebraTensorModule.rTensor W (⋀[W]^n (σ →₀ W)) (ringMap p k B σ a Q f).toLinearMap

theorem coefficient_comp (t : DividedPowerAlgebra QR (σ →₀ QR)) :
    ringMap p k B σ a Q f (CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization.coefficientMap p k B σ a Q s.val t) =
      CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization.coefficientMap p k B σ a Q r.val t := by
  let F := CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a
  let g := Functor.CrystallinePrincipalFunctor.map p k X Q f
  let ps := Functor.CrystallinePrincipalFunctor.projection p k X Q s
  let pr := Functor.CrystallinePrincipalFunctor.projection p k X Q r
  have he : F.map g ≫ F.map ps = F.map pr :=
    (F.map_comp g ps).symm.trans (congrArg F.map (Functor.CrystallinePrincipalFunctor.map_projection p k X Q f))
  have ht := congrArg (fun h : F.obj (Functor.CrystallinePrincipalFunctor.object p k X Q r) ⟶ F.obj Q =>
    h.ambientMap t) he
  exact (congrArg (ringMap p k B σ a Q f)
    (CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization.coefficientMap_apply p k B σ a Q s.val t)).trans
      (ht.trans (CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization.coefficientMap_apply p k B σ a Q r.val t).symm)

theorem moduleMap_comp (n : ℕ) :
    (moduleMap p k B σ a Q f n).comp (CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization.termMap p k B σ a Q s.val n) =
      CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization.termMap p k B σ a Q r.val n := by
  apply LinearMap.restrictScalars_injective W
  apply TensorProduct.ext
  apply LinearMap.ext
  intro t
  apply LinearMap.ext
  intro ω
  change ringMap p k B σ a Q f (CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization.coefficientMap p k B σ a Q s.val t) ⊗ₜ[W] ω =
    CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization.coefficientMap p k B σ a Q r.val t ⊗ₜ[W] ω
  exact congrArg (fun z : Ring p k B σ Q r => z ⊗ₜ[W] ω) (coefficient_comp p k B σ a Q f t)

theorem native_map [Fintype σ] (n : ℕ) :
    (((Koszul.Functor.KoszulFunctor.functor W σ (CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a)
      (CrystallineFrame.Operators.CrystallineFrameOperators.derivative p k B σ a) (CrystallineFrame.Resolution.CrystallineFrameResolution.commute p k B σ a)).map
        (Functor.CrystallinePrincipalFunctor.map p k X Q f).op).f n).hom =
      (moduleMap p k B σ a Q f n).restrictScalars W := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro t
  apply LinearMap.ext
  intro ω
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.FrameMaps.CrystallinePrincipalFrameMaps
