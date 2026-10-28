import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantPolynomialOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantLocalizationIs
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Local Basis And -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalBasisAnd.Construction.LocalBasis

/-!
# Bases on invariant principal opens

Inverting a unit times a power of the determinant turns the corresponding
tuple into a basis. The zero-rank case is included.
-/

open _root_.Module

universe u v w z

variable {A B A' B' : Type*}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B']
variable [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A tuple becomes a basis after localizing at a unit times its determinant
raised to the rank of the module. -/
theorem exists_basis_away (b : Basis ι A B) (x : ι → B) (g : A)
    (v : Aˣ) (hg : g = (v : A) * (b.det x) ^ Fintype.card ι)
    [IsLocalization.Away g A']
    [IsLocalization.Away (algebraMap A B g) B'] :
    ∃ d : Basis ι A' B', ∀ i, d i = algebraMap B B' (x i) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers g)) B' := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  let d := b.localizationLocalization A' (Submonoid.powers g) B'
  have hdet : d.det (fun i => algebraMap B B' (x i)) = algebraMap A A' (b.det x) :=
    InvariantPolynomialOf.Construction.InvariantPolynomial.det_map_of_basis (algebraMap A A') (algebraMap B B')
      (fun a => by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
      b d (fun i => b.localizationLocalization_apply A' (Submonoid.powers g) B' i) x
  have hu : IsUnit (d.det (fun i => algebraMap B B' (x i))) := by
    cases isEmpty_or_nonempty ι with
    | inl h =>
      rw [Basis.det_apply, Matrix.det_isEmpty]
      exact isUnit_one
    | inr h =>
      rw [hdet]
      have hgu : IsUnit (algebraMap A A' g) := IsLocalization.Away.algebraMap_isUnit g
      rw [hg, map_mul, map_pow] at hgu
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_right hgu)
  obtain ⟨hli, hspan⟩ := d.is_basis_iff_det.mpr hu
  exact ⟨Basis.mk hli hspan.ge, fun i => Basis.mk_apply hli hspan.ge i⟩

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantLocalizationIs.Construction.InvariantLocalization
open scoped TensorProduct

/-- On each invariant determinant open, the object algebra is finite free over
its actual invariant ring and the relation algebra is its tensor square. -/
theorem finiteFree_and_tensor_away
    {D : Type*} [CommRing D] [Algebra B D]
    (t : A →+* B) (ht : Function.Injective t) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (b : Basis ι A B) (dp : Basis ι B D) (hdp : ∀ i, dp i = p (b i))
    (x : ι → A) (g : (algebraMap A B).eqLocus t)
    (v : Aˣ) (hg : (g : A) = (v : A) * (b.det (fun i => t (x i))) ^ Fintype.card ι) :
    let A₁ := Localization.Away (g : A)
    let B₁ := Localization.Away (algebraMap A B (g : A))
    let s₁ := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap (algebraMap A B) (g : A) (algebraMap A B (g : A)) rfl
    let t₁ := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap t (g : A) (algebraMap A B (g : A)) g.property.symm
    letI : Algebra A₁ B₁ := s₁.toAlgebra
    let C₁ := s₁.eqLocus t₁
    letI : Algebra C₁ A₁ := C₁.subtype.toAlgebra
    Module.Free C₁ A₁ ∧ Module.Finite C₁ A₁ ∧
      ∃ e : A₁ ⊗[C₁] A₁ ≃ₐ[A₁] B₁,
        ∀ a a', e (a ⊗ₜ[C₁] a') = s₁ a * t₁ a' := by
  let A₁ := Localization.Away (g : A)
  let B₁ := Localization.Away (algebraMap A B (g : A))
  let D₁ := Localization.Away (algebraMap B D (algebraMap A B (g : A)))
  let s₁ := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap (algebraMap A B) (g : A) (algebraMap A B (g : A)) rfl
  let t₁ := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap t (g : A) (algebraMap A B (g : A)) g.property.symm
  let p₁ := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap (algebraMap B D) (algebraMap A B (g : A))
    (algebraMap B D (algebraMap A B (g : A))) rfl
  let p₂ := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap p (algebraMap A B (g : A))
    (algebraMap B D (algebraMap A B (g : A))) (by rw [hp, ← g.property])
  let c₁ := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap c (algebraMap A B (g : A))
    (algebraMap B D (algebraMap A B (g : A))) (hc (g : A))
  let : Algebra A₁ B₁ := s₁.toAlgebra
  let : Algebra B₁ D₁ := p₁.toAlgebra
  have : IsScalarTower A B B₁ := inferInstance
  have : IsScalarTower A A₁ B₁ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A B B₁]
    exact (InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap (algebraMap A B) (g : A) _ rfl a).symm
  have : IsScalarTower B D D₁ := inferInstance
  have : IsScalarTower B B₁ D₁ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply B D D₁]
    exact (InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap (algebraMap B D) (algebraMap A B (g : A)) _ rfl a).symm
  have hp₁ : p₂.comp s₁ = p₁.comp t₁ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (g : A))
    ext a
    simp only [RingHom.comp_apply, s₁, t₁, p₁, p₂, InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap, hp]
  have hc₁ : c₁.comp s₁ = p₁.comp s₁ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (g : A))
    ext a
    simp only [RingHom.comp_apply, s₁, p₁, c₁, InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap, hc]
  have hct₁ : c₁.comp t₁ = p₂.comp t₁ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (g : A))
    ext a
    simp only [RingHom.comp_apply, t₁, p₂, c₁, InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap, hct]
  have : IsLocalization
      (Algebra.algebraMapSubmonoid B (Submonoid.powers (g : A))) B₁ := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have : IsLocalization
      (Algebra.algebraMapSubmonoid D (Submonoid.powers (algebraMap A B (g : A)))) D₁ := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  let b₀ := b.localizationLocalization A₁ (Submonoid.powers (g : A)) B₁
  let dp₀ := dp.localizationLocalization B₁ (Submonoid.powers (algebraMap A B (g : A))) D₁
  have hdp₀ (i : ι) : dp₀ i = p₂ (b₀ i) := by
    simp only [b₀, dp₀, Basis.localizationLocalization_apply, hdp]
    exact (InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap p _ _ (by rw [hp, ← g.property]) (b i)).symm
  obtain ⟨b₁, hb₁⟩ := exists_basis_away (A' := A₁) (B' := B₁)
    b (fun i => t (x i)) (g : A) v hg
  obtain ⟨dp₁, hdp₁⟩ := InvariantPolynomialOf.Construction.InvariantPolynomial.exists_basis_map t₁ p₂
    (RingHom.congr_fun hp₁) b₀ dp₀ hdp₀ b₁
  have hind : LinearIndependent B₁ (fun i => p₂ (b₁ i)) := by
    have he : (fun i => p₂ (b₁ i)) = dp₁ := funext (fun i => (hdp₁ i).symm)
    rw [he]
    exact dp₁.linearIndependent
  apply InvariantBasisOf.Construction.InvariantBasis.finiteFree_and_tensor_of_target_basis t₁
    (InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_injective t (g : A) _ g.property.symm ht) p₂ c₁
    (RingHom.congr_fun hp₁) (RingHom.congr_fun hc₁) (RingHom.congr_fun hct₁)
    (fun i => algebraMap A A₁ (x i)) b₁ _ hind
  intro i
  rw [show t₁ (algebraMap A A₁ (x i)) = algebraMap B B₁ (t (x i)) from
    InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap t (g : A) _ g.property.symm (x i)]
  exact hb₁ i

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalBasisAnd.Construction.LocalBasis
