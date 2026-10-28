import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesSplitting
import Mathlib.RingTheory.Flat.Equalizer

/-! # Local First Cycles Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LocalFirstCyclesSplitting.LocalSectionLifting

noncomputable section

/-! After flat extension to a local ring, first residue cohomology vanishing splits the base change of the original degree-zero kernel inclusion. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u

theorem firstCycles_inclusion_split_after_flat_local_baseChange
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A] [Module.Flat R A]
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    (hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex A (IsLocalRing.ResidueField A)
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A S)).Exact) :
    ∃ r : (A ⊗[R] S.X₁) →ₗ[A] (A ⊗[R] S.f.hom.ker),
      r.comp (S.f.hom.ker.subtype.baseChange A) = LinearMap.id := by
  let T := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A S
  have : Module.Finite A T.X₁ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₁))
  have : Module.Finite A T.X₂ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₂))
  have : Module.Finite A T.X₃ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₃))
  have : Module.Flat A T.X₁ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₁))
  have : Module.Flat A T.X₂ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₂))
  have : Module.Flat A T.X₃ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₃))
  have : Module.Free A T.X₁ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A T.X₂ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A T.X₃ := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr⟩ := Local.FirstCyclesSplitting.LocalSectionLifting.firstCycles_inclusion_split_of_residue_exact T hS
  let e : A ⊗[R] S.f.hom.ker ≃ₗ[A] T.f.hom.ker := S.f.hom.tensorKerEquiv A A
  refine ⟨e.symm.toLinearMap.comp r, ?_⟩
  apply LinearMap.ext
  intro x
  have he : (e x).val = (S.f.hom.ker.subtype.baseChange A) x :=
    LinearMap.tensorKer_coe A A S.f.hom x
  have hh : r (e x).val = e x := congrArg (fun k => k (e x)) hr
  change e.symm (r ((S.f.hom.ker.subtype.baseChange A) x)) = x
  exact (congrArg (fun y => e.symm (r y)) he.symm).trans
    ((congrArg e.symm hh).trans (e.symm_apply_apply x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LocalFirstCyclesSplitting.LocalSectionLifting
