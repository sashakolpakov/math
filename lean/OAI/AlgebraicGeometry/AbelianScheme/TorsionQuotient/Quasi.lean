import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Quasi -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry

/-!
# Geometric properties of the actual TorsionQuotient torsion kernel

These lemmas concern the equalizer used by the repaired statement. No TorsionQuotient
statement stub is imported. Prime-to-characteristic unramifiedness and
flatness, and the subgroup-parameter construction, remain separate work.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

/-- A finite-type formally unramified morphism has discrete algebraic fibers. -/
theorem locallyQuasiFinite_of_formallyUnramified
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f where
  quasiFinite_appLE := by
    intro U hU V hV e
    let p := (f.appLE U V e).hom
    let : Algebra Γ(Y, U) Γ(X, V) := p.toAlgebra
    have hu : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) :=
      f.formallyUnramified_appLE hU hV e
    have ht : Algebra.FiniteType Γ(Y, U) Γ(X, V) := f.finiteType_appLE hU hV e
    let : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) := hu
    let : Algebra.FiniteType Γ(Y, U) Γ(X, V) := ht
    exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

/-- Proper formally unramified morphisms are finite. -/
theorem finite_of_proper_formallyUnramified
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [FormallyUnramified f] : IsFinite f := by
  let : LocallyQuasiFinite f := locallyQuasiFinite_of_formallyUnramified f
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite f).mpr ⟨inferInstance, inferInstance⟩

variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

/-- For a separated group scheme, the actual m-torsion inclusion is closed. -/
theorem torsion_closedImmersion [IsSeparated A.hom] (m : ℕ) :
    IsClosedImmersion (SubgroupFunctor.torsionι A m).left := by
  unfold SubgroupFunctor.torsionι
  exact isClosedImmersion_equalizer_ι_left ((𝟙 A : A ⟶ A) ^ m) (1 : A ⟶ A)

/-- Properness of the group scheme implies properness of its torsion kernel. -/
theorem torsion_isProper [IsProper A.hom] (m : ℕ) :
    IsProper (SubgroupFunctor.torsionScheme A m).hom := by
  let : IsClosedImmersion (SubgroupFunctor.torsionι A m).left := torsion_closedImmersion A m
  have h : IsProper ((SubgroupFunctor.torsionι A m).left ≫ A.hom) := inferInstance
  simpa only [Over.w] using h

/-- In particular, torsion kernels are quasi-compact over the base. -/
theorem torsion_quasiCompact [IsProper A.hom] (m : ℕ) :
    QuasiCompact (SubgroupFunctor.torsionScheme A m).hom := by
  let : IsProper (SubgroupFunctor.torsionScheme A m).hom := torsion_isProper A m
  infer_instance

/-- Multiplication by an integer on a proper group scheme is proper. -/
theorem power_isProper [IsProper A.hom] (m : ℕ) :
    IsProper (((𝟙 A : A ⟶ A) ^ m).left) := by
  have h : IsProper ((((𝟙 A : A ⟶ A) ^ m).left) ≫ A.hom) := by
    simpa only [Over.w] using (inferInstance : IsProper A.hom)
  let : IsProper ((((𝟙 A : A ⟶ A) ^ m).left) ≫ A.hom) := h
  exact IsProper.of_comp _ A.hom

/-- The m = 1 kernel is canonically the base, via the identity section. -/
noncomputable def torsionOneIso : SubgroupFunctor.torsionScheme A 1 ≅ 𝟙_ (Over S) where
  hom := toUnit _
  inv := SubgroupFunctor.torsionLift 1 (1 : 𝟙_ (Over S) ⟶ A) (one_pow 1)
  hom_inv_id := by
    apply equalizer.hom_ext
    change toUnit (SubgroupFunctor.torsionScheme A 1) ≫ SubgroupFunctor.torsionLift 1 (1 : 𝟙_ (Over S) ⟶ A)
      (one_pow 1) ≫ SubgroupFunctor.torsionι A 1 = 𝟙 (SubgroupFunctor.torsionScheme A 1) ≫ SubgroupFunctor.torsionι A 1
    rw [SubgroupFunctor.torsionLift_ι, MonObj.comp_one, Category.id_comp]
    have h := (SubgroupFunctor.factors_through_torsion_iff 1 (SubgroupFunctor.torsionι A 1)).mp
      ⟨𝟙 _, Category.id_comp _⟩
    simpa only [pow_one] using h.symm
  inv_hom_id := by
    apply isTerminalTensorUnit.hom_ext

/-- The base structure map of A[1] is an isomorphism. -/
theorem torsion_one_isIso : IsIso (SubgroupFunctor.torsionScheme A 1).hom := by
  have h : (torsionOneIso A).hom.left = (SubgroupFunctor.torsionScheme A 1).hom := rfl
  rw [← h]
  change IsIso (((Over.forget S).mapIso (torsionOneIso A)).hom)
  infer_instance

/-- The boundary case m = 1 of the torsion conclusion. -/
theorem torsion_one_finite_etale :
    IsFinite (SubgroupFunctor.torsionScheme A 1).hom ∧ Etale (SubgroupFunctor.torsionScheme A 1).hom := by
  let : IsIso (SubgroupFunctor.torsionScheme A 1).hom := torsion_one_isIso A
  exact ⟨inferInstance, inferInstance⟩

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry
