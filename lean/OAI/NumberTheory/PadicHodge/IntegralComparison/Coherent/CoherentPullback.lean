import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.BinaryBiproduct
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasicoherentKernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Cokernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Coproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionGeneratingSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteGeneratingSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeQuotient
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.Finiteness.Prod

/-! # Coherent Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.CoherentPullback

noncomputable section

/-! Finite-type quasicoherent module sheaves on a locally Noetherian
scheme are closed under the categorical pullbacks used in resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (M N : X.Modules)
  [M.IsQuasicoherent] [N.IsQuasicoherent]

local instance : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

theorem biprod_quasicoherent : (M ⊞ N).IsQuasicoherent :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.BinaryBiproduct.module_biprod_quasicoherent M N

variable [M.IsFiniteType] [N.IsFiniteType]

theorem biprod_finiteType : (M ⊞ N).IsFiniteType := by
  let := biprod_quasicoherent M N
  apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections.module_finiteType_of_affine_sections_finite (M ⊞ N)
  intro U
  let F := Affine.ModuleExactSections.sections U.val
  let : F.Additive := Affine.ModuleExactSections.additive U.val
  let : PreservesBinaryBiproduct M N F := preservesBinaryBiproduct_of_preservesBiproduct F M N
  let : Module.Finite Γ(X, U.val) (F.obj M) :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite M U
  let : Module.Finite Γ(X, U.val) (F.obj N) :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite N U
  let e := Functor.mapBiprod F M N ≪≫ ModuleCat.biprodIsoProd (F.obj M) (F.obj N)
  exact Module.Finite.equiv e.symm.toLinearEquiv

variable {M N} {P : X.Modules} [P.IsQuasicoherent] (f : M ⟶ P) (g : N ⟶ P)

def kernelIso : pullback f g ≅ kernel (biprod.desc f (-g)) :=
  (limit.isoLimitCone ⟨_, Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g⟩).symm

omit [SheafOfModules.IsFiniteType M] [SheafOfModules.IsFiniteType N] in
theorem quasicoherent : (pullback f g).IsQuasicoherent := by
  let := biprod_quasicoherent M N
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (kernelIso f g).symm
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels.module_quasicoherent_kernel (biprod.desc f (-g)))

variable [IsLocallyNoetherian X]

theorem finiteType : (pullback f g).IsFiniteType := by
  let := biprod_quasicoherent M N
  let := biprod_finiteType M N
  let := quasicoherent f g
  let := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels.module_quasicoherent_kernel (biprod.desc f (-g))
  let := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType (biprod.desc f (-g))
  exact IntegralComparison.Module.FiniteTypeQuotient.of_epi (kernelIso f g).inv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.CoherentPullback
