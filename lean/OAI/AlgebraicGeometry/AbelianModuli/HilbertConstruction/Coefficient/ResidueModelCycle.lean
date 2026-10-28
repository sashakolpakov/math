import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOneTensor

/-! # Residue Model Cycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ResidueModelCycle

noncomputable section

/-! A nonzero section in the coefficient-residue fiber, together with
cycle lifting, supplies a global model cycle surviving in the actual fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

theorem residueLift_exists_surviving_cycle
    {R B M N : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : B ≃ₗ[R] IsLocalRing.ResidueField R) (he : e 1 = 1) (d : M →ₗ[R] N)
    [Nontrivial (d.lTensor B).ker]
    (hlift : ∀ z : IsLocalRing.ResidueField R ⊗[R] M,
      d.baseChange (IsLocalRing.ResidueField R) z = 0 →
      ∃ x : M, d x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z) :
    ∃ x : M, d x = 0 ∧ (1 : B) ⊗ₜ[R] x ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_ne (0 : (d.lTensor B).ker)
  have hne : (e.rTensor M) z.val ≠ 0 := by
    intro h
    apply hz
    apply Subtype.ext
    exact (e.rTensor M).injective (h.trans (e.rTensor M).map_zero.symm)
  have hc : d.baseChange (IsLocalRing.ResidueField R) ((e.rTensor M) z.val) = 0 := by
    have h := LinearMap.congr_fun (ReferenceFamily.Tensor.CoefficientEquivalence.tensorCoefficientEquiv_natural e d) z.val
    exact h.trans (by
      change (e.rTensor N) ((d.lTensor B) z.val) = 0
      rw [z.property, map_zero])
  obtain ⟨x, hx, hxn⟩ := hlift _ hc
  refine ⟨x, hx, fun hzero => hne ?_⟩
  calc
    (e.rTensor M) z.val = (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x := hxn.symm
    _ = (e.rTensor M) ((1 : B) ⊗ₜ[R] x) := by
      change _ = e 1 ⊗ₜ[R] x
      rw [he]
    _ = 0 := by rw [hzero, map_zero]

theorem coefficientSectionsEquiv_one
    (S : Scheme.{u}) [IsAffine S] (K : Type u) [Field K] [Algebra Γ(S, ⊤) K] :
    ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldSectionsEquiv S K 1 = 1 := by
  change (Scheme.ΓSpecIso (.of K)).hom.hom 1 = 1
  exact map_one _

theorem extended_first_kernel_nontrivial
    {R B : Type u} [CommRing R] [CommRing B] (a : R →+* B)
    (D : CochainComplex (ModuleCat.{u} R) ℕ)
    (hn : Nontrivial ((((ModuleCat.extendScalars a).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D).d 0 1).hom.ker) :
    let : Algebra R B := a.toAlgebra
    Nontrivial ((D.d 0 1).hom.lTensor B).ker := hn

theorem extendedComplex_exists_surviving_cycle
    {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B]
    (D : CochainComplex (ModuleCat.{u} R) ℕ) (a : R →+* B) :
    let : Algebra R B := a.toAlgebra
    ∀ (e : B ≃ₗ[R] IsLocalRing.ResidueField R) (_he : e 1 = 1)
      (_hn : Nontrivial ((((ModuleCat.extendScalars a).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D).d 0 1).hom.ker)
      (_hlift : ∀ z : IsLocalRing.ResidueField R ⊗[R] D.X 0,
        (D.d 0 1).hom.baseChange (IsLocalRing.ResidueField R) z = 0 →
        ∃ x : D.X 0, D.d 0 1 x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z),
      ∃ x : D.X 0, D.d 0 1 x = 0 ∧ (1 : B) ⊗ₜ[R] x ≠ 0 := by
  let : Algebra R B := a.toAlgebra
  dsimp only
  intro e he hn hlift
  have : Nontrivial ((D.d 0 1).hom.lTensor B).ker := extended_first_kernel_nontrivial a D hn
  exact residueLift_exists_surviving_cycle e he (D.d 0 1).hom hlift

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ResidueModelCycle
