import OAI.AlgebraicGeometry.FormalGeometry.Completion.Cohomology
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Cohomology Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback

/-!
# Completion: the linear Frobenius action on geometric H¹

The action is induced by the actual scheme morphism using exact inverse
image on the pro-étale sites. Scalar compatibility is proved before
extending coefficients; no cohomological weights are assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

namespace Construction

noncomputable section

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}}

theorem proEtCoefficientToPushforward_scalar (f : X ⟶ Y) (a : ℤ_[ℓ]) :
    Cohomology.Construction.liftedEllAdicScalar ℓ Y a ≫ ProetalePullback.Construction.proEtCoefficientToPushforward ℓ f =
      ProetalePullback.Construction.proEtCoefficientToPushforward ℓ f ≫
        ((ProetalePullback.Construction.proEtBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (Cohomology.Construction.liftedEllAdicScalar ℓ X a) := by
  ext U s
  rfl

theorem proEtCoefficientPullback_scalar (f : X ⟶ Y) (a : ℤ_[ℓ]) :
    (ProetalePullback.Construction.proEtSheafPullback f).map (Cohomology.Construction.liftedEllAdicScalar ℓ Y a) ≫
      ProetalePullback.Construction.proEtCoefficientPullback ℓ f =
        ProetalePullback.Construction.proEtCoefficientPullback ℓ f ≫ Cohomology.Construction.liftedEllAdicScalar ℓ X a := by
  exact ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv_naturality_right_square
      (Cohomology.Construction.liftedEllAdicScalar ℓ Y a) (ProetalePullback.Construction.proEtCoefficientToPushforward ℓ f)
      (ProetalePullback.Construction.proEtCoefficientToPushforward ℓ f) (Cohomology.Construction.liftedEllAdicScalar ℓ X a)
      (proEtCoefficientToPushforward_scalar ℓ f a)

theorem integralEllAdicPullback_apply (f : X ⟶ Y) (n : ℕ)
    (x : Y.EllAdicCohomology ℓ n) :
    ProetalePullback.Construction.integralEllAdicPullback ℓ f n x =
      ((Abelian.Ext.mk₀ ((ProetalePullback.Construction.proEtConstantPullbackIso f).inv.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).comp
          (x.mapExactFunctor (ProetalePullback.Construction.proEtSheafPullback f)) (zero_add n)).comp
        (Abelian.Ext.mk₀ (ProetalePullback.Construction.proEtCoefficientPullback ℓ f)) (add_zero n) := rfl

theorem integralEllAdicPullback_smul (f : X ⟶ Y) (n : ℕ)
    (a : ℤ_[ℓ]) (x : Y.EllAdicCohomology ℓ n) :
    ProetalePullback.Construction.integralEllAdicPullback ℓ f n (a • x) = a • ProetalePullback.Construction.integralEllAdicPullback ℓ f n x := by
  change (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ Y).H n at x
  change ProetalePullback.Construction.integralEllAdicPullback ℓ f n
      (x.comp (Abelian.Ext.mk₀ (Cohomology.Construction.liftedEllAdicScalar ℓ Y a)) (add_zero n)) =
    (ProetalePullback.Construction.integralEllAdicPullback ℓ f n x).comp
      (Abelian.Ext.mk₀ (Cohomology.Construction.liftedEllAdicScalar ℓ X a)) (add_zero n)
  erw [integralEllAdicPullback_apply, integralEllAdicPullback_apply]
  simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    proEtCoefficientPullback_scalar]
  rfl

/-- Pullback is linear for the constructed ℤ_ℓ-module structures. -/
def integralEllAdicPullbackLinear (f : X ⟶ Y) (n : ℕ) :
    Y.EllAdicCohomology ℓ n →ₗ[ℤ_[ℓ]] X.EllAdicCohomology ℓ n where
  __ := ProetalePullback.Construction.integralEllAdicPullback ℓ f n
  map_smul' := integralEllAdicPullback_smul ℓ f n

/-- Pullback after extending coefficients to the algebraic closure of ℚ_ℓ. -/
def algebraicEllAdicH1Pullback (f : X ⟶ Y) :
    Cohomology.Construction.EllAdicH1AlgebraicCoefficients ℓ Y →ₗ[AlgebraicClosure ℚ_[ℓ]]
      Cohomology.Construction.EllAdicH1AlgebraicCoefficients ℓ X :=
  (integralEllAdicPullbackLinear ℓ f 1).baseChange (AlgebraicClosure ℚ_[ℓ])

/-- The actual geometric degree-one Frobenius operator. -/
def geometricH1Frobenius
    (k : Type u) [Field k] [Fintype k] (A : Over (Spec (CommRingCat.of k))) :
    Module.End (AlgebraicClosure ℚ_[ℓ]) (Cohomology.Construction.GeometricH1 ℓ A) :=
  algebraicEllAdicH1Pullback ℓ (Geometric.Frobenius.Construction.geometricSchemeFrobenius k A)

/-- A realization of H¹ identifies F with pullback by the q-power scheme
Frobenius. This replaces the proposed interface without including weights. -/
def IsEtaleH1GeometricFrobenius
    {k : Type u} [Field k] [Fintype k] (A : Over (Spec (CommRingCat.of k)))
    {H : Type v} [AddCommGroup H] [Module (AlgebraicClosure ℚ_[ℓ]) H]
    (F : Module.End (AlgebraicClosure ℚ_[ℓ]) H) : Prop :=
  ∃ e : Cohomology.Construction.GeometricH1 ℓ A ≃ₗ[AlgebraicClosure ℚ_[ℓ]] H,
    ∀ x, F (e x) = e (geometricH1Frobenius ℓ k A x)

/-- Eigenvalues in a realization are eigenvalues of the actual geometric operator. -/
theorem realized_eigenvalue
    {k : Type u} [Field k] [Fintype k] (A : Over (Spec (CommRingCat.of k)))
    {H : Type v} [AddCommGroup H] [Module (AlgebraicClosure ℚ_[ℓ]) H]
    (F : Module.End (AlgebraicClosure ℚ_[ℓ]) H)
    (hF : IsEtaleH1GeometricFrobenius ℓ A F)
    (α : AlgebraicClosure ℚ_[ℓ]) (hα : F.HasEigenvalue α) :
    (geometricH1Frobenius ℓ k A).HasEigenvalue α := by
  obtain ⟨e, he⟩ := hF
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm v)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · apply e.injective
    rw [← he, e.map_smul, e.apply_symm_apply]
    exact hv.apply_eq_smul
  · intro hzero
    apply hv.2
    have h := congrArg e hzero
    simpa using h

end

end Construction

/-- The formerly proposed predicate, with the argument order used by the
immutable specification. Its content is identification with actual H¹
and its constructed Frobenius action, without weight assumptions. -/
abbrev IsEtaleH1GeometricFrobenius
    {k : Type u} [Field k] [Fintype k] (A : Over (Spec (CommRingCat.of k)))
    (ℓ : ℕ) [Fact ℓ.Prime]
    {H : Type v} [AddCommGroup H] [Module (AlgebraicClosure ℚ_[ℓ]) H]
    (F : Module.End (AlgebraicClosure ℚ_[ℓ]) H) : Prop :=
  Construction.IsEtaleH1GeometricFrobenius ℓ A F

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback
