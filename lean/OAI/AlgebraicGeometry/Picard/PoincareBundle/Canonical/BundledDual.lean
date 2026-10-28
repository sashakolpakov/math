import OAI.AlgebraicGeometry.Picard.PoincareBundle.GivenDualGroupCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionTypedIsogeny

/-! # Bundled Dual -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.BundledDual

noncomputable section

/-! The given bundled dual and isogeny retain their actual maps and kernel type in the Picard-derived group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

section

private theorem bundled_congr {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D E : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A.scheme) (h : D = E)
    (hd : SmoothOfRelativeDimension g D.abelian.hom) (he : SmoothOfRelativeDimension g E.abelian.hom) :
    D.toBundled A hd = E.toBundled A he := by
  cases h
  rfl

variable {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

/-- Rebundle the actual Picard-derived dual using the given smooth relative dimension. -/
def canonical : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A :=
  (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.toBundled A D.abelian.smoothDimension

/-- Rigidity makes this entire normalized bundled dual equal to the original data. -/
theorem canonical_eq : canonical D = D := by
  exact (bundled_congr (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)
    (DualDataEquality.withPicardGroup_eq (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D))
    D.abelian.smoothDimension D.abelian.smoothDimension).trans (by cases D; rfl)

/-- The original isogeny uses exactly the same scheme morphism in the canonical dual group. -/
def isogeny (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A (canonical D).abelian where
  hom := f.hom
  preservesGroup := by
    have : IsMonHom (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from f.hom) := f.preservesGroup
    exact GivenDualGroupCompatibility.isMonHom (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) f.hom
  finite := f.finite
  flat := f.flat
  surjective := f.surjective

private theorem type_of_target_eq {S : Scheme} {g : ℕ} {A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (h : B = C) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (hr : HEq f.hom r.hom) (δ : Fin g → ℕ) : f.HasPolarizationType δ ↔ r.HasPolarizationType δ := by
  cases h
  have hf := SharedTorsionTypedIsogeny.isogeny_ext f r (eq_of_heq hr)
  cases hf
  rfl

end

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

/-- All native finite-kernel invariants defining polarization type are preserved. -/
theorem hasPolarizationType (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (δ : Fin g → ℕ) :
    (isogeny D f).HasPolarizationType δ ↔ f.HasPolarizationType δ :=
  type_of_target_eq (congrArg (fun E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A => E.abelian) (canonical_eq D))
    (isogeny D f) f HEq.rfl δ

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.BundledDual
