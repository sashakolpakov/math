import OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormOpenIs
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Scheme Norm -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen

/-!
# Norm neighborhoods on affine schemes

For a finite-free affine morphism, the norm of a global section cuts out
the locus over which the entire fiber avoids that section's zero set.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (s : Y ⟶ X)

noncomputable def norm (a : Γ(Y, ⊤)) : Γ(X, ⊤) :=
  letI := s.appTop.hom.toAlgebra
  Algebra.norm Γ(X, ⊤) a

theorem mem_basicOpen_norm {ι : Type v} [Fintype ι]
    (b : letI := s.appTop.hom.toAlgebra; Module.Basis ι Γ(X, ⊤) Γ(Y, ⊤))
    (a : Γ(Y, ⊤)) (x : X) :
    x ∈ X.basicOpen (SchemeNormOpen.norm s a) ↔ ∀ y : Y, s y = x → y ∈ Y.basicOpen a := by
  let := s.appTop.hom.toAlgebra
  let := Module.Free.of_basis b
  let := Module.Finite.of_basis b
  let p : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom x
  have hc (y : Y) :
      PrimeSpectrum.comap (algebraMap Γ(X, ⊤) Γ(Y, ⊤)) (Y.isoSpec.hom y) =
        X.isoSpec.hom (s y) :=
    congrArg (fun f => f y) (Scheme.isoSpec_hom_naturality s)
  rw [← X.map_PrimeSpectrum_basicOpen_of_affine]
  change Algebra.norm Γ(X, ⊤) a ∉ p.asIdeal ↔ _
  rw [NormOpenIs.Construction.NormOpen.norm_notMem_iff (R := Γ(X, ⊤)) (A := Γ(Y, ⊤)) p a]
  constructor
  · intro h y hy
    rw [← Y.map_PrimeSpectrum_basicOpen_of_affine]
    exact h (Y.isoSpec.hom y) ((hc y).trans (congrArg X.isoSpec.hom hy))
  · intro h q hq
    have he : s (Y.isoSpec.inv q) = x := by
      have hq' : Y.isoSpec.hom (Y.isoSpec.inv q) = q := Scheme.inv_hom_apply Y.isoSpec q
      have hh : X.isoSpec.hom (s (Y.isoSpec.inv q)) = X.isoSpec.hom x :=
        (hc _).symm.trans ((congrArg _ hq').trans hq)
      simpa only [Scheme.hom_inv_apply] using congrArg X.isoSpec.inv hh
    have hy := h (Y.isoSpec.inv q) he
    rw [← Y.map_PrimeSpectrum_basicOpen_of_affine] at hy
    change a ∉ (Y.isoSpec.hom (Y.isoSpec.inv q)).asIdeal at hy
    have hq' : (Y.isoSpec.hom (Y.isoSpec.inv q) : PrimeSpectrum Γ(Y, ⊤)) = q :=
      Scheme.inv_hom_apply Y.isoSpec q
    exact hq' ▸ hy

/-- The complement of the finite image of a principal zero set is affine. -/
theorem basicOpen_norm_eq {ι : Type v} [Fintype ι]
    (b : letI := s.appTop.hom.toAlgebra; Module.Basis ι Γ(X, ⊤) Γ(Y, ⊤))
    (a : Γ(Y, ⊤)) :
    (X.basicOpen (SchemeNormOpen.norm s a) : Set X) = (s '' (Y.basicOpen a : Set Y)ᶜ)ᶜ := by
  ext x
  change x ∈ X.basicOpen (SchemeNormOpen.norm s a) ↔ _
  rw [mem_basicOpen_norm s b]
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
  exact ⟨fun h y hy hs => hy (h y hs), fun h y hs => by
    by_contra hy
    exact h y hy hs⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen
