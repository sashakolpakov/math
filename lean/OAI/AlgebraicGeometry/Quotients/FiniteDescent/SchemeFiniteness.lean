import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatFiniteness
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Scheme Finiteness -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeFiniteness.Construction.SchemeFinitenessDescent

/-!
# Local finite presentation of the quotient over its base

Local finite presentation descends from the source through a finite locally
free surjection. The proof works over arbitrary schemes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Affine form of local finite-presentation descent through a finite
locally free surjection. -/
theorem locallyOfFinitePresentation_affine
    {X Q S : Scheme.{u}} [IsAffine Q] [IsAffine S]
    (q : X ⟶ Q) (b : Q ⟶ S)
    [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    [LocallyOfFinitePresentation (q ≫ b)] : LocallyOfFinitePresentation b := by
  have : IsAffine X := isAffine_of_isAffineHom q
  let := b.appTop.hom.toAlgebra
  let := q.appTop.hom.toAlgebra
  let := (q.appTop.hom.comp b.appTop.hom).toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(Q, ⊤) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite Γ(Q, ⊤) Γ(X, ⊤) := q.finite_appTop
  have : Module.Flat Γ(Q, ⊤) Γ(X, ⊤) := q.flat_appTop
  have : Algebra.FinitePresentation Γ(Q, ⊤) Γ(X, ⊤) := q.finitePresentation_appTop
  have : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) := (q ≫ b).finitePresentation_appTop
  have h : b.appTop.hom.FinitePresentation := FlatFiniteness.Construction.FlatFinitenessDescent.finitePresentation
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp
      ⟨inferInstance, inferInstance⟩).injective
  have : LocallyOfFinitePresentation (Spec.map b.appTop) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr h
  have heq : b = Q.isoSpec.hom ≫ Spec.map b.appTop ≫ S.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

/-- Local finite presentation descends through a finite locally free
surjective morphism of schemes. -/
theorem locallyOfFinitePresentation
    {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    [LocallyOfFinitePresentation (q ≫ b)] : LocallyOfFinitePresentation b := by
  constructor
  intro U hU V hV e
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have : Surjective (q ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict q V).flip inferInstance
  have hcomp : LocallyOfFinitePresentation ((q ∣_ V) ≫ b.resLE U V e) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
    infer_instance
  have : LocallyOfFinitePresentation (b.resLE U V e) :=
    locallyOfFinitePresentation_affine (q ∣_ V) (b.resLE U V e)
  exact (RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso b U V e)).mp (b.resLE U V e).finitePresentation_appTop

/-- Affine form of flatness descent through a finite
locally free surjection. -/
theorem flat_affine
    {X Q S : Scheme.{u}} [IsAffine Q] [IsAffine S]
    (q : X ⟶ Q) (b : Q ⟶ S)
    [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    [Flat (q ≫ b)] : Flat b := by
  have : IsAffine X := isAffine_of_isAffineHom q
  let := b.appTop.hom.toAlgebra
  let := q.appTop.hom.toAlgebra
  let := (q.appTop.hom.comp b.appTop.hom).toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(Q, ⊤) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite Γ(Q, ⊤) Γ(X, ⊤) := q.finite_appTop
  have : Module.Flat Γ(Q, ⊤) Γ(X, ⊤) := q.flat_appTop
  have : Algebra.FinitePresentation Γ(Q, ⊤) Γ(X, ⊤) := q.finitePresentation_appTop
  have : Module.Flat Γ(S, ⊤) Γ(X, ⊤) := (q ≫ b).flat_appTop
  have h : b.appTop.hom.Flat := FlatFiniteness.Construction.FlatFinitenessDescent.flat
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp
      ⟨inferInstance, inferInstance⟩).injective
  have : Flat (Spec.map b.appTop) :=
    Flat.SpecMap_iff.mpr h
  have heq : b = Q.isoSpec.hom ≫ Spec.map b.appTop ≫ S.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

/-- Flatness descends through a finite locally free
surjective morphism of schemes. -/
theorem flat
    {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    [Flat (q ≫ b)] : Flat b := by
  constructor
  intro U hU V hV e
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have : Surjective (q ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict q V).flip inferInstance
  have hcomp : Flat ((q ∣_ V) ≫ b.resLE U V e) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
    infer_instance
  have : Flat (b.resLE U V e) :=
    flat_affine (q ∣_ V) (b.resLE U V e)
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso b U V e)).mp (b.resLE U V e).flat_appTop

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeFiniteness.Construction.SchemeFinitenessDescent
