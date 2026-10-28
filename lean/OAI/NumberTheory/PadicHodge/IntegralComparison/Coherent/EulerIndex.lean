import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.KTheory
import OAI.AlgebraicGeometry.SheafCohomology.Projective.EulerRange

/-! # Euler Index -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerIndex.ProjectiveK

noncomputable section

/-! The actual coherent Euler characteristic, computed by the finite
projective affine Čech cover, descends to the coherent Grothendieck group.
The definition uses the original sheaf and its actual direct image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ} {A : Scheme.{u}}
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f]

def coherentEuler (M : A.Modules) : ℤ :=
  AlgebraicGeometry.SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler ((Scheme.Modules.pushforward f).obj M)

omit [IsClosedImmersion f] in
theorem coherentEuler_eq_of_iso {M N : A.Modules} (e : M ≅ N) :
    coherentEuler f M = coherentEuler f N :=
  AlgebraicGeometry.SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler_eq_of_iso ((Scheme.Modules.pushforward f).mapIso e)

theorem coherentEuler_add_of_shortExact (T : ShortComplex A.Modules) (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    [T.X₁.IsFiniteType] [T.X₂.IsFiniteType] [T.X₃.IsFiniteType] :
    coherentEuler f T.X₂ = coherentEuler f T.X₁ + coherentEuler f T.X₃ := by
  let S := T.map (Scheme.Modules.pushforward f)
  have : S.X₁.IsQuasicoherent := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage_quasicoherent f T.X₁
  have : S.X₂.IsQuasicoherent := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage_quasicoherent f T.X₂
  have : S.X₃.IsQuasicoherent := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage_quasicoherent f T.X₃
  have : S.X₁.IsFiniteType := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage_finiteType f T.X₁
  have : S.X₂.IsFiniteType := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage_finiteType f T.X₂
  have : S.X₃.IsFiniteType := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage_finiteType f T.X₃
  exact AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.projectiveEuler_add_of_shortExact S (AlgebraicGeometry.FormalGeometry.Completion.Affine.PushforwardExact.Construction.affineModulePushforward_shortExact f hT)

def coherentEulerOnFree : FreeAbelianGroup (KTheory.Projective.CoherentModule A) →+ ℤ :=
  FreeAbelianGroup.lift (fun M => coherentEuler f M.sheaf)

theorem coherentK0Relations_le_eulerKernel :
    KTheory.Projective.coherentK0Relations A ≤ (coherentEulerOnFree f).ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro _ ⟨S, rfl⟩
  change coherentEulerOnFree f (KTheory.Projective.coherentExactRelation S) = 0
  simp only [coherentEulerOnFree, KTheory.Projective.coherentExactRelation, map_sub,
    FreeAbelianGroup.lift_apply_of]
  have he := coherentEuler_add_of_shortExact f
    (ShortComplex.mk S.inclusion S.projection S.zero) S.shortExact
  change coherentEuler f S.middle.sheaf =
    coherentEuler f S.left.sheaf + coherentEuler f S.right.sheaf at he
  rw [he]
  abel

def coherentEulerIndex : KTheory.Projective.CoherentK0 A →+ ℤ :=
  QuotientAddGroup.lift (KTheory.Projective.coherentK0Relations A) (coherentEulerOnFree f)
    (coherentK0Relations_le_eulerKernel f)

@[simp]
theorem coherentEulerIndex_class (M : KTheory.Projective.CoherentModule A) :
    coherentEulerIndex f (KTheory.Projective.coherentK0Class M) = coherentEuler f M.sheaf := by
  change coherentEulerOnFree f (FreeAbelianGroup.of M) = _
  exact FreeAbelianGroup.lift_apply_of _ _

@[simp]
theorem coherentEulerIndex_tensor_class (L : A.Modules)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) (M : KTheory.Projective.CoherentModule A) :
    coherentEulerIndex f (KTheory.Projective.coherentTensorK0 L hL (KTheory.Projective.coherentK0Class M)) =
      coherentEuler f (KTheory.Projective.coherentTensorModule L hL M).sheaf := by
  rw [KTheory.Projective.coherentTensorK0_class, coherentEulerIndex_class]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerIndex.ProjectiveK
