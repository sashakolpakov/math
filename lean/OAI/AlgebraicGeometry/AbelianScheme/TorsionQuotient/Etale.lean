import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.PowerLocal
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothCriterion
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FinitePresentationOf
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Left
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale.TorsionEtale

/-!
# TorsionQuotient: finite etaleness of actual abelian-scheme torsion

The multiplication morphism has the local infinitesimal lifting property,
is locally of finite presentation, and is formally unramified. Its torsion
kernel is its actual pullback along the identity section.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A] [Smooth A.hom]
variable (n : ℕ) (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x))

omit [IsCommMonObj A] in
theorem power_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (((𝟙 A : A ⟶ A) ^ n).left) := by
  have h : LocallyOfFinitePresentation ((((𝟙 A : A ⟶ A) ^ n).left) ≫ A.hom) := by
    simpa only [Over.w] using (inferInstance : LocallyOfFinitePresentation A.hom)
  let : LocallyOfFinitePresentation ((((𝟙 A : A ⟶ A) ^ n).left) ≫ A.hom) := h
  exact FinitePresentationOf.FinitePresentation.of_comp _ A.hom

include hn in
theorem power_smooth : Smooth (((𝟙 A : A ⟶ A) ^ n).left) := by
  let : LocallyOfFinitePresentation (((𝟙 A : A ⟶ A) ^ n).left) :=
    power_locallyOfFinitePresentation A n
  apply SmoothCriterion.SchemeSmoothCriterion.smooth_of_local_lifts
  intro C B hC hB p hp hker a b hab
  exact PowerLocal.PowerLocalLifting.exists_scheme_power_lift A p hp hker n hn a b hab

include hn in
/-- Multiplication by an invertible integer on a smooth commutative group
scheme is etale, without any affine hypothesis. -/
theorem power_etale : Etale (((𝟙 A : A ⟶ A) ^ n).left) := by
  let : Smooth (((𝟙 A : A ⟶ A) ^ n).left) := power_smooth A n hn
  let : FormallyUnramified (((𝟙 A : A ⟶ A) ^ n).left) :=
    Power.PowerGeometry.power_formallyUnramified A n hn
  exact Etale.of_formallyUnramified_of_flat _

include hn in
/-- The actual equalizer defining n-torsion is etale over the base. -/
theorem torsion_etale : Etale (SubgroupFunctor.torsionScheme A n).hom := by
  let : Etale (((𝟙 A : A ⟶ A) ^ n).left) := power_etale A n hn
  exact MorphismProperty.of_isPullback (P := @Etale)
    (Left.TorsionPullback.isPullback_left A n) inferInstance

include hn in
/-- The full torsion conclusion for an abelian scheme. In fact only
properness, smoothness, and the commutative group law are needed. -/
theorem torsion_finite_etale [IsProper A.hom] :
    IsFinite (SubgroupFunctor.torsionScheme A n).hom ∧ Etale (SubgroupFunctor.torsionScheme A n).hom :=
  ⟨Power.PowerGeometry.torsion_isFinite A n hn, torsion_etale A n hn⟩

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale.TorsionEtale
