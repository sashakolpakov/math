import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackTorsionRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.FunctionRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.BaseChangeFunctionSheaf

/-! # Pullback Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackRigidity

noncomputable section

/-! Full-level rigidity on arbitrary base changes of a finite-type pure
family in characteristic zero. Geometric rigidity and actual functions
detect the entire automorphism, including on nonreduced tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem purePullback_abelian_eq_id
    {K : Type} [Field K] [CharZero K] [Countable K]
    {X S : Scheme.{0}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N X)
    (hN : 3 ≤ N) (t : S ⟶ X)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) (A.pullback t)) :
    e.abelian.hom = 𝟙 (A.abelian.pullback t).scheme := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let B := A.abelian.pullback t
  let q : B.scheme ⟶ B.scheme := e.abelian.hom
  have : IsMonHom q := inferInstanceAs (IsMonHom e.abelian.hom)
  let d : B.scheme ⟶ B.scheme := q / 𝟙 B.scheme
  have hΓ (V : S.Opens) : IsIso (B.scheme.hom ∣_ V).appTop := by
    apply (HilbertConstruction.FunctionSheafAffineCriterion.morphismRestrict_appTop_isIso_iff B.scheme.hom V).mpr
    exact Abelian.BaseChangeFunctionSheaf.abelian_baseChange_function_app_isIso A.abelian
      (pullback.fst A.abelian.scheme.hom t) (pullback.snd A.abelian.scheme.hom t) t
      (IsPullback.of_hasPullback A.abelian.scheme.hom t) V
  have hzero : η[B.scheme] ≫ d = η[B.scheme] := by
    rw [show d = q / 𝟙 B.scheme from rfl,
      GrpObj.comp_div, IsMonHom.one_hom, Category.comp_id, div_self']
    simp only [Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp]
  have hd : d = 1 := Geometric.FunctionRigidity.overHom_eq_one_of_geometricPoints B.scheme B.scheme hΓ d hzero (by
    intro k _ _ x y
    have he := PullbackTorsionRigidity.purePullback_geometric_abelian_eq_id p A hN t x (e.pullback x)
    have hx := Geometric.FunctionRigidity.overHom_fieldPoint_eq_of_baseChange q (𝟙 B.scheme) x
      (he.trans ((Over.pullback x).map_id B.scheme).symm) y
    rw [show d = q / 𝟙 B.scheme from rfl, GrpObj.comp_div, hx, div_self'])
  change q = 𝟙 B.scheme
  exact div_eq_one.mp hd

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackRigidity
