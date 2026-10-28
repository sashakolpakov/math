import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FiberVanishing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FiberResidueExactness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ResidueKernelBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import OAI.AlgebraicGeometry.SheafCohomology.Projective.QuasicoherentAffinePullback

/-! # Concrete Fiber Cycle Lifting -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConcreteFiberCycleLifting

noncomputable section

/-! Vanishing of actual first fiber cohomology makes all degree-zero
residue cycles come from tensors of cycles of the original model. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

universe u

theorem model_actualFiber_residue_exact
    {X S : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    (f : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (ha : ∀ i, IsAffineOpen (U i))
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U) (x : S)
    [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (f.fiberι x) f (f.fiberToSpecResidueField x)
      (S.fromSpecResidueField x) (f.fiber_fac x) M U φ) 1]
    [Subsingleton (SheafCohomology.AffineH.Projective.H ((Scheme.Modules.pullback (f.fiberι x)).obj M) 1)] :
    letI : Algebra Γ(S, ⊤) (S.presheaf.stalk x) :=
      (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
    (Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex (S.presheaf.stalk x)
      (IsLocalRing.ResidueField (S.presheaf.stalk x))
      (Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex Γ(S, ⊤) (S.presheaf.stalk x)
        (D.sc' 0 1 2))).Exact := by
  have : IsAffineHom (f.fiberι x) :=
    MorphismProperty.pullback_fst f (S.fromSpecResidueField x) inferInstance
  have : ((Scheme.Modules.pullback (f.fiberι x)).obj M).IsQuasicoherent :=
    SheafCohomology.Projective.QuasicoherentAffinePullback.quasicoherent_pullback_of_isAffineHom (f.fiberι x) M
  have : (f.fiber x).IsSeparated :=
    ⟨by rw [← terminal.comp_from (f.fiberι x)]; infer_instance⟩
  apply FiberResidueExactness.fiber_model_residue_exact S x D
  exact FiberVanishing.model_baseChange_exactAt_of_fiber_vanishing (f.fiberι x) f
    (f.fiberToSpecResidueField x) (S.fromSpecResidueField x) (f.fiber_fac x) M U hU
    (fun i => (ha i).preimage (f.fiberι x)) φ 1

theorem actualFiber_residue_cycle_mem_original_kernel_range
    {X S : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    (f : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (ha : ∀ i, IsAffineOpen (U i))
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U) (x : S)
    [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
    [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
    [Module.Finite Γ(S, ⊤) (D.X 2)] [Module.Projective Γ(S, ⊤) (D.X 2)]
    [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (f.fiberι x) f (f.fiberToSpecResidueField x)
      (S.fromSpecResidueField x) (f.fiber_fac x) M U φ) 1]
    [Subsingleton (SheafCohomology.AffineH.Projective.H ((Scheme.Modules.pullback (f.fiberι x)).obj M) 1)] :
    letI : Algebra Γ(S, ⊤) (S.presheaf.stalk x) :=
      (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
    ∀ z : IsLocalRing.ResidueField (S.presheaf.stalk x) ⊗[S.presheaf.stalk x]
      ((S.presheaf.stalk x) ⊗[Γ(S, ⊤)] D.X 0),
      ((D.d 0 1).hom.baseChange (S.presheaf.stalk x)).baseChange
        (IsLocalRing.ResidueField (S.presheaf.stalk x)) z = 0 →
      z ∈ (((D.d 0 1).hom.ker.subtype.baseChange (S.presheaf.stalk x)).baseChange
        (IsLocalRing.ResidueField (S.presheaf.stalk x))).range := by
  let : Algebra Γ(S, ⊤) (S.presheaf.stalk x) :=
    (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : Module.Flat Γ(S, ⊤) (S.presheaf.stalk x) := Quotients.FiniteDescent.FiberScalar.Construction.FiberScalarMaps.stalk_flat S x
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₁ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 0))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₁ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 0))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₂ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 1))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₂ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 1))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₃ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 2))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₃ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 2))
  exact ResidueKernelBaseChange.residue_cycle_mem_original_kernel_range (D.sc' 0 1 2)
    (model_actualFiber_residue_exact f M U hU ha φ x)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConcreteFiberCycleLifting
