import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDimension
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Power
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryQuotients

/-! # Constructed Quotient Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
The constructed geometric quotient carries its native isogeny, full
prime-to-kernel marking, descended integral action, and preserved q-rank.
These constructions use the exact scheme kernel and its proven bounds.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable {H : Grp (Over (Spec (.of k)))} {i : H.X ⟶ A.scheme}

variable (Q : GeometricQuotient.Construction.GeometricKernelQuotient A H i)

def GeometricQuotient.Construction.GeometricKernelQuotient.isogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q.abelian where
  hom := Q.projection
  preservesGroup := Q.groupHom
  finite := Q.finite
  flat := Q.flat
  surjective := Q.surjective

theorem GeometricQuotient.Construction.GeometricKernelQuotient.qRank_preserved (q : ℕ) [IsFinite (A.torsionScheme q).hom] :
    Nat.card (A.torsionPoints q (Over.mk (𝟙 _))) =
      Nat.card (Q.abelian.torsionPoints q (Over.mk (𝟙 _))) :=
  OrdinaryQuotients.Construction.isogeny_qRank_preserved A Q.abelian Q.isogeny q

/-- The quotient's actual kernel inherits the multiplier bound of the
embedded subgroup, on every test scheme. -/
theorem GeometricQuotient.Construction.GeometricKernelQuotient.kernel_killed (m : ℕ)
    (hi : ∀ (T : Over (Spec (.of k))) (h : T ⟶ H.X), (h ≫ i) ^ m = 1)
    (T : Over (Spec (.of k))) (x : T ⟶ A.scheme) (hx : x ≫ Q.isogeny.hom = 1) :
    x ^ m = 1 := by
  obtain ⟨h, hh, _⟩ := (Q.kernel T x).mp hx
  exact (congrArg (fun a => a ^ m) hh).symm.trans (hi T h)

def GeometricQuotient.Construction.GeometricKernelQuotient.level {m N : ℕ} (hmN : Nat.Coprime m N)
    (hi : ∀ (T : Over (Spec (.of k))) (h : T ⟶ H.X), (h ≫ i) ^ m = 1)
    (ell : A.FullLevel N) : Q.abelian.FullLevel N :=
  Power.Construction.quotientLevel Q.isogeny hmN (Q.kernel_killed m hi) ell

theorem GeometricQuotient.Construction.GeometricKernelQuotient.level_transports {m N : ℕ} (hmN : Nat.Coprime m N)
    (hi : ∀ (T : Over (Spec (.of k))) (h : T ⟶ H.X), (h ≫ i) ^ m = 1)
    (ell : A.FullLevel N) (T : (Over (Spec (.of k)))ᵒᵖ)
    (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N (Spec (.of k))).obj T) :
    ((Q.level hmN hi ell).hom.app T c).val = (ell.hom.app T c).val ≫ Q.projection :=
  Power.Construction.quotientLevel_transports Q.isogeny hmN (Q.kernel_killed m hi) ell T c

variable {R : Type v} [CommRing R]

/-- Stability of the embedded subgroup supplies stability of the actual
quotient kernel; no action on the target is assumed. -/
theorem GeometricQuotient.Construction.GeometricKernelQuotient.actionStableKernel_of_subgroup [Mono i]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (hi : ∀ (r : R) (T : Over (Spec (.of k))) (h : T ⟶ H.X),
      ∃ h' : T ⟶ H.X, h' ≫ i = (h ≫ i) ≫ ρ.map r) :
    QuotientActionBase.Construction.ActionStableKernel ρ Q.isogeny := by
  intro r T x hx
  obtain ⟨h, hh, _⟩ := (Q.kernel T x).mp hx
  obtain ⟨h', hh'⟩ := hi r T h
  have hfact : h' ≫ i = x ≫ ρ.map r := hh'.trans (congrArg (fun a => a ≫ ρ.map r) hh)
  exact (Q.kernel T _).mpr
    ⟨h', hfact, fun b hb => (cancel_mono i).mp (hb.trans hfact.symm)⟩

def GeometricQuotient.Construction.GeometricKernelQuotient.action [Mono i] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (hi : ∀ (r : R) (T : Over (Spec (.of k))) (h : T ⟶ H.X),
      ∃ h' : T ⟶ H.X, h' ≫ i = (h ≫ i) ≫ ρ.map r) : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R Q.abelian :=
  QuotientActionBase.Construction.quotientAction ρ Q.isogeny (Q.actionStableKernel_of_subgroup ρ hi)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
