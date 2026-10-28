import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalBasisAnd
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DeterminantCoverEq
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Flat Invariants -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatInvariants.Construction.FiniteFlatInvariants

/-!
# Finite flatness over the invariant ring

The invariant determinant opens cover the invariant spectrum. On each open,
the object ring is finite free by the local basis argument. Localization
descent gives a finite, flat, finitely presented algebra over the invariant ring.
-/

open _root_.Module

universe u v w z

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantLocalizationIs.Construction.InvariantLocalization

variable {A : Type u} {B : Type v} {D : Type w} {ι : Type z}
variable [CommRing A] [CommRing B] [CommRing D]
variable [Algebra A B] [Algebra B D] [Fintype ι] [DecidableEq ι]

/-- A finite-free relation diagram whose target-valued elements span its
relation algebra makes the object algebra finite, flat and finitely presented
over its invariant subring. -/
theorem finite_flat_finitelyPresented
    (t : A →+* B) (ht : Function.Injective t) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (b : Basis ι A B) (dp dc : Basis ι B D)
    (hdp : ∀ i, dp i = p (b i)) (hdc : ∀ i, dc i = c (b i))
    (hspan : Submodule.span A (Set.range t) = ⊤) :
    let C := (algebraMap A B).eqLocus t
    letI : Algebra C A := C.subtype.toAlgebra
    Module.Finite C A ∧ Module.Flat C A ∧ Algebra.FinitePresentation C A := by
  classical
  let C := (algebraMap A B).eqLocus t
  let : Algebra C A := C.subtype.toAlgebra
  obtain ⟨g, hcover, hg⟩ := DeterminantCoverEq.Construction.DeterminantCover.exists_invariant_cover
    t ht p c hp hc hct b dp dc hdp hdc hspan
  let S : Set C := Set.range g
  let A₁ (r : S) := Localization.Away ((r : C) : A)
  let C₁ (r : S) := InvariantLocalizationIs.Construction.InvariantLocalization.awayInvariants (algebraMap A B) t (r : C)
  let : ∀ r : S, Algebra C (C₁ r) := fun r =>
    (InvariantLocalizationIs.Construction.InvariantLocalization.awayInvariantMap (algebraMap A B) t (r : C)).toAlgebra
  let : ∀ r : S, Algebra (C₁ r) (A₁ r) := fun r => (C₁ r).subtype.toAlgebra
  have : ∀ r : S, IsLocalization.Away (r : C) (C₁ r) := fun r =>
    InvariantLocalizationIs.Construction.InvariantLocalization.isLocalization_awayInvariants (algebraMap A B) t (r : C)
  have : ∀ r : S, IsScalarTower C (C₁ r) (A₁ r) := fun r =>
    InvariantLocalizationIs.Construction.InvariantLocalization.scalarTower_awayInvariants (algebraMap A B) t (r : C)
  have hlocal (r : S) : Module.Free (C₁ r) (A₁ r) ∧ Module.Finite (C₁ r) (A₁ r) := by
    rcases r with ⟨_, x, rfl⟩
    obtain ⟨v, hv⟩ := hg x
    have h := LocalBasisAnd.Construction.LocalBasis.finiteFree_and_tensor_away t ht p c hp hc hct b dp hdp
      x (g x) v hv
    exact ⟨h.1, h.2.1⟩
  let f (r : S) : A →ₗ[C] A₁ r := (IsScalarTower.toAlgHom C A (A₁ r)).toLinearMap
  have : ∀ r : S, IsLocalizedModule.Away (r : C) (f r) := by
    intro r
    have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers (r : C)))
        (A₁ r) := by
      rw [Algebra.algebraMapSubmonoid_powers]
      change IsLocalization.Away ((r : C) : A) (Localization.Away ((r : C) : A))
      infer_instance
    exact inferInstance
  have hfinite : Module.Finite C A :=
    Module.Finite.of_localizationSpan' (Rₚ := fun r => ↥(C₁ r)) S hcover f
      (fun r => (hlocal r).2)
  have hfp : Module.FinitePresentation C A :=
    Module.FinitePresentation.of_localizationSpan' (Rₚ := fun r => ↥(C₁ r)) S hcover f (fun r => by
      have := (hlocal r).1
      have := (hlocal r).2
      exact Module.finitePresentation_of_projective (C₁ r) (A₁ r))
  refine ⟨hfinite, ?_, Algebra.FinitePresentation.of_finitePresentation C A⟩
  apply Module.flat_of_isLocalized_span (R := C) C A S hcover A₁ f
  intro r
  have := (hlocal r).1
  have : Module.Flat (C₁ r) (A₁ r) := inferInstance
  have : Module.Flat C (C₁ r) := IsLocalization.flat (C₁ r) (Submonoid.powers (r : C))
  exact Module.Flat.trans C (C₁ r) (A₁ r)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatInvariants.Construction.FiniteFlatInvariants
