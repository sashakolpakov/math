import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.CharZero.Defs

/-! # Unit -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit.Construction

/-!
Explicit IsogenyQuotient prerequisite propositions. TorsionQuotientInput copies the repaired
Statements/TorsionQuotient.lean specification, including its uliftYoneda conclusion.
The statement theorem itself is not imported or invoked as a proved fact.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The supplied TorsionQuotient proposition, using its actual torsion and subgroup functor. -/
def TorsionQuotientInput : Prop :=
  ∀ {S : Scheme.{u}} (A : Over S)
    [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (m : ℕ) (_hm : 0 < m)
    (_hm_unit : ∀ s : S, IsUnit (m : S.presheaf.stalk s))
    (M : Type u) [AddCommGroup M] [Module (ZMod m) M] [Finite M],
    IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A m).hom ∧
    Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A m).hom ∧
    ∃ P : Over S,
      IsFinite P.hom ∧ Etale P.hom ∧
      Nonempty (uliftYoneda.{u + 1}.obj P ≅ TorsionQuotient.SubgroupFunctor.subgroupChoiceFunctor A m M)

/-- Every positive integer is invertible on every scheme over a
characteristic-zero field, including on nonreduced test schemes. -/
theorem positive_integer_unit_on_characteristic_zero_base
    {K : Type u} [Field K] [CharZero K]
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
    (m : ℕ) (hm : 0 < m) (x : S) : IsUnit (m : S.presheaf.stalk x) := by
  let constants : K →+* Γ(S, ⊤) :=
    s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let toStalk : K →+* S.presheaf.stalk x :=
    (S.presheaf.germ ⊤ x (by trivial)).hom.comp constants
  have hmK : IsUnit (m : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))
  simpa only [map_natCast] using hmK.map toStalk

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit.Construction
