import OAI.ArithmeticGeometry.Descent.CMVariety.Faithfulness
import OAI.ArithmeticGeometry.Descent.CMVariety.Canonical
import Mathlib.LinearAlgebra.Countable

/-! # Countable Group Maps -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.CountableGroupMaps.Abelian.IntrinsicPeriods

noncomputable section

/-!
There are only countably many actual algebraic group morphisms between
two fixed complex abelian varieties. Faithfulness and finite dimensionality
of their actual rational H¹ provide the countable encoding.
-/

open _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

theorem algebraic_group_maps_countable (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Countable {f : A.toOver ⟶ B.toOver // IsMonHom f} := by
  let : FiniteDimensional ℚ (A.variety.rationalCohomology 1) := (Canonical.Abelian.IntrinsicPeriods.canonicalH1 A).finiteDimensional
  let : FiniteDimensional ℚ (B.variety.rationalCohomology 1) := (Canonical.Abelian.IntrinsicPeriods.canonicalH1 B).finiteDimensional
  let : Countable (B.variety.rationalCohomology 1 →ₗ[ℚ] A.variety.rationalCohomology 1) :=
    Finsupp.Countable.of_moduleFinite (R := ℚ)
  apply Function.Injective.countable
    (f := fun f : {f : A.toOver ⟶ B.toOver // IsMonHom f} => AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f.val)
  intro f g hfg
  let : IsMonHom f.val := f.property
  let : IsMonHom g.val := g.property
  exact Subtype.ext (Faithfulness.Abelian.IntrinsicPeriods.algebraic_group_map_eq_of_h1Pullback_eq f.val g.val hfg)

theorem algebraic_group_isos_countable (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Countable {e : A.toOver ≅ B.toOver // IsMonHom e.hom} := by
  let : Countable {f : A.toOver ⟶ B.toOver // IsMonHom f} := algebraic_group_maps_countable A B
  apply Function.Injective.countable (f := fun e : {e : A.toOver ≅ B.toOver // IsMonHom e.hom} =>
    (⟨e.val.hom, e.property⟩ : {f : A.toOver ⟶ B.toOver // IsMonHom f}))
  intro e f h
  exact Subtype.ext (Iso.ext (congrArg Subtype.val h))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.CountableGroupMaps.Abelian.IntrinsicPeriods
