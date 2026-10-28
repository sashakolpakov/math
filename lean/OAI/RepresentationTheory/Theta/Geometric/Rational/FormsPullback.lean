import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsPrimitive
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseProjectivity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension

/-! # Forms Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Rational endomorphisms act on the actual Albanese one-forms by
the unique pullback compatible with every positive denominator clearing. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)

local instance Data.ActiveHeckeThetaData.rationalForms_group : GrpObj D.pel.complexAlbanese.X := D.pel.complexAlbanese.grp
local instance Data.ActiveHeckeThetaData.rationalForms_comm : IsCommMonObj D.pel.complexAlbanese.X := D.pel.complexAlbanese.comm
local instance Data.ActiveHeckeThetaData.rationalForms_addGroup : AddCommGroup D.pel.OneFormsA :=
  Module.addCommMonoidToAddCommGroup ℂ

include hg in
theorem Data.ActiveHeckeThetaData.pullbackForms_add (a b : D.pel.EndK) :
    D.pel.pullbackForms (a + b) = D.pel.pullbackForms a + D.pel.pullbackForms b := by
  apply LinearMap.ext
  intro ω
  unfold AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.pullbackForms
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endSchemeMap_add, Functor.map_mul]
  exact AlgebraicGeometry.AbelianScheme.TateComparison.FormsPrimitive.abelian_formsPullback_mul (D.pel.actualComplexAlbaneseVariety hg)
    (D.pel.actualComplexAlbaneseVariety hg).variety _ _ ω

include hg in
theorem Data.ActiveHeckeThetaData.pullbackForms_zero : D.pel.pullbackForms 0 = 0 := by
  have h := D.pullbackForms_add hg 0 0
  rw [zero_add] at h
  exact (add_left_cancel (a := D.pel.pullbackForms 0) ((add_zero _).trans h)).symm

def Data.ActiveHeckeThetaData.integralFormsPullbackAddHom : D.pel.EndK →+ Module.End ℂ D.pel.OneFormsA where
  toFun := D.pel.pullbackForms
  map_zero' := D.pullbackForms_zero hg
  map_add' := D.pullbackForms_add hg

def Data.ActiveHeckeThetaData.rationalFormsPullback : D.pel.EndQ →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA :=
  AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom (D.integralFormsPullbackAddHom hg)

theorem Data.ActiveHeckeThetaData.rationalFormsPullback_integral (a : D.pel.EndK) :
    D.rationalFormsPullback hg (D.pel.toRational a) = D.pel.pullbackForms a := by
  change AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom (D.integralFormsPullbackAddHom hg) (1 ⊗ₜ[ℤ] a) = _
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom_tmul, one_smul]
  rfl

theorem Data.ActiveHeckeThetaData.rationalFormsPullback_spec (a : D.pel.EndQ) :
    D.IsRationalFormsPullback a (D.rationalFormsPullback hg a) := by
  obtain ⟨n, hn, b, hb⟩ := D.pel.endQ_positive_denominator a
  refine ⟨⟨n, hn, b, hb⟩, ?_⟩
  intro m _ b hb
  have h := congrArg (D.rationalFormsPullback hg) hb
  rw [map_nsmul, Data.ActiveHeckeThetaData.rationalFormsPullback_integral] at h
  exact (Nat.cast_smul_eq_nsmul ℂ m _).trans h

theorem Data.ActiveHeckeThetaData.rationalFormsPullback_unique (a : D.pel.EndQ) (f g : Module.End ℂ D.pel.OneFormsA)
    (hf : D.IsRationalFormsPullback a f) (hg' : D.IsRationalFormsPullback a g) : f = g := by
  obtain ⟨n, hn, b, hb⟩ := hf.1
  have h := (hf.2 n hn b hb).trans (hg'.2 n hn b hb).symm
  exact (smul_right_injective (M := Module.End ℂ D.pel.OneFormsA)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))) h

def Data.ActiveHeckeThetaData.heckeRationalForms (A : TateComparison.Action D.pel) :
    SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA :=
  (D.rationalFormsPullback hg).comp A.algebraAction.toLinearMap

theorem Data.ActiveHeckeThetaData.heckeRationalForms_spec (A : TateComparison.Action D.pel) (h : SphericalGU.Spherical.FullHecke q s) :
    D.IsRationalFormsPullback (A.algebraAction h) (D.heckeRationalForms hg A h) :=
  D.rationalFormsPullback_spec hg (A.algebraAction h)

include hg in
theorem Data.ActiveHeckeThetaData.exists_heckeRationalForms (A : TateComparison.Action D.pel) :
    ∃ rhoForms : SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA,
      ∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rhoForms h) :=
  ⟨D.heckeRationalForms hg A, D.heckeRationalForms_spec hg A⟩

end

end OAI.RepresentationTheory.Theta.Geometric
