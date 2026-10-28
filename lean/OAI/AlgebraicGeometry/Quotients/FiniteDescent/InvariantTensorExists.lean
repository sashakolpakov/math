import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalBasisAnd
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DeterminantCoverEq
import Mathlib.RingTheory.LocalProperties.Exactness

/-! # Invariant Tensor Exists -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantTensorExists.Construction.InvariantTensor

/-!
# Effectiveness of the invariant-ring quotient

The canonical map from the tensor square over invariants to the relation ring
is an isomorphism. We descend the explicitly compatible local tensor
equivalences along the invariant determinant cover.
-/

open _root_.Module
open scoped TensorProduct

universe u v w z

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantLocalizationIs.Construction.InvariantLocalization

variable {A : Type u} {B : Type v} {D : Type w} {ι : Type z}
variable [CommRing A] [CommRing B] [CommRing D]
variable [Algebra A B] [Algebra B D] [Fintype ι] [DecidableEq ι]

/-- The tensor square over the invariant ring is the relation algebra, with
the specified source and target maps. -/
theorem exists_tensor_equiv
    (t : A →+* B) (ht : Function.Injective t) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (b : Basis ι A B) (dp dc : Basis ι B D)
    (hdp : ∀ i, dp i = p (b i)) (hdc : ∀ i, dc i = c (b i))
    (hspan : Submodule.span A (Set.range t) = ⊤) :
    let C := (algebraMap A B).eqLocus t
    letI : Algebra C A := C.subtype.toAlgebra
    ∃ e : A ⊗[C] A ≃ₐ[A] B, ∀ a a', e (a ⊗ₜ[C] a') = algebraMap A B a * t a' := by
  classical
  let C := (algebraMap A B).eqLocus t
  let : Algebra C A := C.subtype.toAlgebra
  let : Algebra C B := ((algebraMap A B).comp C.subtype).toAlgebra
  have : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let tC : A →ₐ[C] B := { t with commutes' := fun r => r.property.symm }
  let F : A ⊗[C] A →ₗ[C] B := (tC.liftEquiv C A A B).toLinearMap.restrictScalars C
  obtain ⟨g, hcover, hg⟩ := DeterminantCoverEq.Construction.DeterminantCover.exists_invariant_cover
    t ht p c hp hc hct b dp dc hdp hdc hspan
  let S : Set C := Set.range g
  let A₁ (r : S) := Localization.Away ((r : C) : A)
  let B₁ (r : S) := Localization.Away (algebraMap A B ((r : C) : A))
  let C₁ (r : S) := InvariantLocalizationIs.Construction.InvariantLocalization.awayInvariants (algebraMap A B) t (r : C)
  let s₁ (r : S) := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap (algebraMap A B) ((r : C) : A)
    (algebraMap A B ((r : C) : A)) rfl
  let t₁ (r : S) := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap t ((r : C) : A)
    (algebraMap A B ((r : C) : A)) (r : C).property.symm
  let : ∀ r : S, Algebra C (C₁ r) := fun r =>
    (InvariantLocalizationIs.Construction.InvariantLocalization.awayInvariantMap (algebraMap A B) t (r : C)).toAlgebra
  let : ∀ r : S, Algebra (C₁ r) (A₁ r) := fun r => (C₁ r).subtype.toAlgebra
  let : ∀ r : S, Algebra (A₁ r) (B₁ r) := fun r => (s₁ r).toAlgebra
  let : ∀ r : S, Algebra (C₁ r) (B₁ r) := fun r =>
    Algebra.compHom (B₁ r) (C₁ r).subtype
  have : ∀ r : S, IsLocalization.Away (r : C) (C₁ r) := fun r =>
    InvariantLocalizationIs.Construction.InvariantLocalization.isLocalization_awayInvariants (algebraMap A B) t (r : C)
  have : ∀ r : S, IsScalarTower C (C₁ r) (A₁ r) := fun r =>
    InvariantLocalizationIs.Construction.InvariantLocalization.scalarTower_awayInvariants (algebraMap A B) t (r : C)
  have : ∀ r : S, IsScalarTower (C₁ r) (A₁ r) (B₁ r) := fun _ =>
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : ∀ r : S, IsScalarTower C (A₁ r) (B₁ r) := fun r =>
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply C B (B₁ r)]
      change algebraMap B (B₁ r) (algebraMap A B (a : A)) =
        s₁ r (algebraMap A (A₁ r) (a : A))
      exact (InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap (algebraMap A B) _ _ rfl (a : A)).symm
  have : ∀ r : S, IsScalarTower C (C₁ r) (B₁ r) := fun r =>
    IsScalarTower.to₁₂₄ C (C₁ r) (A₁ r) (B₁ r)
  let fA (r : S) : A →ₗ[C] A₁ r := (IsScalarTower.toAlgHom C A (A₁ r)).toLinearMap
  let fB (r : S) : B →ₗ[C] B₁ r := (IsScalarTower.toAlgHom C B (B₁ r)).toLinearMap
  have : ∀ r : S, IsLocalizedModule.Away (r : C) (fA r) := by
    intro r
    have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers (r : C)))
        (A₁ r) := by
      rw [Algebra.algebraMapSubmonoid_powers]
      change IsLocalization.Away ((r : C) : A) (Localization.Away ((r : C) : A))
      infer_instance
    infer_instance
  have : ∀ r : S, IsLocalizedModule.Away (r : C) (fB r) := by
    intro r
    have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers (r : C)))
        (B₁ r) := by
      rw [Algebra.algebraMapSubmonoid_powers]
      change IsLocalization.Away (algebraMap A B ((r : C) : A))
        (Localization.Away (algebraMap A B ((r : C) : A)))
      infer_instance
    infer_instance
  let E₁ (r : S) := A₁ r ⊗[C] A₁ r
  let fE (r : S) : A ⊗[C] A →ₗ[C] E₁ r := TensorProduct.map (fA r) (fA r)
  have : ∀ r : S, IsLocalizedModule.Away (r : C) (fE r) := fun _ => inferInstance
  have hbij : Function.Bijective F := by
    apply bijective_of_isLocalized_span S hcover E₁ fE B₁ fB F
    intro r
    obtain ⟨e, he⟩ : ∃ e : A₁ r ⊗[C₁ r] A₁ r ≃ₐ[A₁ r] B₁ r,
        ∀ a a', e (a ⊗ₜ[C₁ r] a') = s₁ r a * t₁ r a' := by
      rcases r with ⟨_, x, rfl⟩
      obtain ⟨v, hv⟩ := hg x
      exact (LocalBasisAnd.Construction.LocalBasis.finiteFree_and_tensor_away t ht p c hp hc hct b dp hdp
        x (g x) v hv).2.2
    have : TensorProduct.CompatibleSMul C (C₁ r) (A₁ r) (A₁ r) :=
      IsLocalization.tensorProduct_compatibleSMul (Submonoid.powers (r : C))
        (C₁ r) (A₁ r) (A₁ r)
    let E : E₁ r ≃ₗ[C] B₁ r :=
      (TensorProduct.equivOfCompatibleSMul (C₁ r) C C (A₁ r) (A₁ r)).trans
        (e.toLinearEquiv.restrictScalars C)
    have hE : IsLocalizedModule.map (Submonoid.powers (r : C)) (fE r) (fB r) F =
        E.toLinearMap := by
      apply IsLocalizedModule.linearMap_ext (Submonoid.powers (r : C)) (fE r) (fB r)
      ext a a'
      change IsLocalizedModule.map (Submonoid.powers (r : C)) (fE r) (fB r) F
        (fE r (a ⊗ₜ[C] a')) = E (fE r (a ⊗ₜ[C] a'))
      rw [IsLocalizedModule.map_apply]
      have hF : F (a ⊗ₜ[C] a') = algebraMap A B a * t a' := Algebra.smul_def a (t a')
      have hfE : fE r (a ⊗ₜ[C] a') = fA r a ⊗ₜ[C] fA r a' :=
        TensorProduct.map_tmul (fA r) (fA r) a a'
      have hEtmul (x y : A₁ r) : E (x ⊗ₜ[C] y) = e (x ⊗ₜ[C₁ r] y) := rfl
      rw [hF, hfE, hEtmul]
      change algebraMap B (B₁ r) (algebraMap A B a * t a') =
        e (algebraMap A (A₁ r) a ⊗ₜ[C₁ r] algebraMap A (A₁ r) a')
      rw [he, map_mul]
      exact congrArg₂ (· * ·) (InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap (algebraMap A B) _ _ rfl a).symm
        (InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap t _ _ (r : C).property.symm a').symm
    rw [hE]
    exact E.bijective
  refine ⟨AlgEquiv.ofBijective (tC.liftEquiv C A A B) hbij, ?_⟩
  intro a a'
  exact Algebra.smul_def a (t a')

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantTensorExists.Construction.InvariantTensor
