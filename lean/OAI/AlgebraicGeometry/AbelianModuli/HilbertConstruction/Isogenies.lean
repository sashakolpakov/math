import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Isogenies -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Finite flat isogenies and the tame geometric kernel type of a polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open scoped BigOperators

universe u

variable {g h : ℕ} {S : Scheme.{u}}

/-- A group-scheme morphism acts on test-scheme points. -/
def Abelian.Schemes.AbelianScheme.mapPoints (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] (T : Over S) :
    A.Points T →* B.Points T where
  toFun a := a ≫ f
  map_one' := MonObj.one_comp f
  map_mul' a b := MonObj.mul_comp a b f

/-- An isogeny is a finite, flat, surjective morphism of group schemes. -/
structure Abelian.Schemes.AbelianScheme.Isogeny (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S) where
  hom : A.scheme ⟶ B.scheme
  preservesGroup : IsMonHom hom
  finite : IsFinite hom.left
  flat : Flat hom.left
  surjective : Surjective hom.left

attribute [instance] Abelian.Schemes.AbelianScheme.Isogeny.preservesGroup Abelian.Schemes.AbelianScheme.Isogeny.finite Abelian.Schemes.AbelianScheme.Isogeny.flat Abelian.Schemes.AbelianScheme.Isogeny.surjective

/-- The identity is an isogeny. -/
def Abelian.Schemes.AbelianScheme.Isogeny.identity (A : Abelian.Schemes.AbelianScheme g S) : Abelian.Schemes.AbelianScheme.Isogeny A A where
  hom := 𝟙 A.scheme
  preservesGroup := inferInstance
  finite := inferInstanceAs (IsFinite (𝟙 A.scheme.left))
  flat := inferInstanceAs (Flat (𝟙 A.scheme.left))
  surjective := inferInstanceAs (Surjective (𝟙 A.scheme.left))

/-- Kernel points over a test scheme. -/
def Abelian.Schemes.AbelianScheme.Isogeny.kernelAt {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
    (f : Abelian.Schemes.AbelianScheme.Isogeny A B) (T : Over S) : Subgroup (A.Points T) :=
  (A.mapPoints B f.hom T).ker

/-- Polarization type includes both finite-flat degree and elementary divisors of
geometric kernel points. The degree condition retains nonreduced kernel length,
which geometric points alone cannot detect in positive characteristic. -/
structure Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme g S}
    (f : Abelian.Schemes.AbelianScheme.Isogeny A B) (δ : Fin g → ℕ) : Prop where
  degree : ∀ b : B.scheme.left, f.hom.left.finrank b = (∏ i, δ i) ^ 2
  geometricKernel : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    Nonempty (f.kernelAt (Over.mk s) ≃*
      Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i))))

/-- An isogeny of principal polarization type is an isomorphism. -/
theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.principal_isIso {A B : Abelian.Schemes.AbelianScheme g S}
    {f : Abelian.Schemes.AbelianScheme.Isogeny A B} (hf : f.HasPolarizationType (fun _ => 1)) : IsIso f.hom.left := by
  apply (Scheme.Hom.isIso_iff_finrank_eq f.hom.left).mpr
  funext b
  simpa using hf.degree b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
