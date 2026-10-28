import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.ResidueEvaluation

/-! # Global Function Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.GlobalFunctionResidue

noncomputable section

/-! The original crystalline residue map with its actual, unlifted Witt-vector scalar action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra PeriodInvariants.WittAlgebraFunctor.residueAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X 0

def map : M →ₗ[W] A := by
  let l : M →ₗ[R] ZeroLevel.GlobalFunctionLinear.coefficientModule p k X :=
    SmoothProper.CrystallineResidueInjection.integralEvaluation p k X hprojective
  let v : M → Γ(X.left, ⊤) := fun x => (l x).down
  refine { toFun := v, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    exact congrArg ULift.down (l.map_add x y)
  · intro w x
    have h := congrArg ULift.down (l.map_smul (ULift.up w : R) x)
    change v ((ULift.up w : R) • x) =
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X ⊤ (WittVector.constantCoeff w) * v x at h
    have hs : (w • x : M) = (ULift.up w : R) • x := rfl
    have ht : (w • (v x : A) : A) =
        AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X ⊤ (WittVector.constantCoeff w) * v x := rfl
    exact (congrArg v hs).trans (h.trans ht.symm)

theorem constants (w : WittVector p A) :
    map p k X hprojective (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective w) =
      w.coeff 0 := congrArg ULift.down (GlobalFunction.ResidueEvaluation.evaluation p k X hprojective w)

omit [Nonempty X.left] in
theorem kernel : LinearMap.ker (map p k X hprojective) =
    (Ideal.span {(p : W)}) • (⊤ : Submodule W M) := by
  have hm (x : M) : x ∈ (Ideal.span {(p : W)}) • (⊤ : Submodule W M) ↔ ∃ y : M, (p : W) • y = x := by
    simpa only [Principal.PowerModuleSequence.submodule, pow_one] using
      Principal.PowerModuleSequence.mem_submodule W M (p : W) 1 x
  have hr (x : M) : x ∈ (Ideal.span {(p : R)}) • (⊤ : Submodule R M) ↔ ∃ y : M, (p : R) • y = x := by
    simpa only [Principal.PowerModuleSequence.submodule, pow_one] using
      Principal.PowerModuleSequence.mem_submodule R M (p : R) 1 x
  ext x
  have hz : map p k X hprojective x = 0 ↔
      SmoothProper.CrystallineResidueInjection.integralEvaluation p k X hprojective x = 0 := by
    constructor
    · intro h
      apply ULift.ext
      exact h
    · exact congrArg ULift.down
  rw [LinearMap.mem_ker, hz, ← LinearMap.mem_ker,
    SmoothProper.CrystallineResidueInjection.integralEvaluation_kernel p k X hprojective, hr, hm]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hy⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.GlobalFunctionResidue
