import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.IsomorphismParameterBaseChange

/-! # Isomorphism Base Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli

noncomputable section

/-! Transport of a moduli isomorphism across equal base maps conjugates its abelian component by the corresponding pullback comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Isomorphisms.LevelPreservingIso.baseEquality_abelian_hom
    {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f h : T ⟶ S) (w : f = h)
    (e : Isomorphisms.LevelPreservingIso (A.pullback f) (B.pullback f)) :
    ((congrArg (fun b => Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b)) w).mp e).abelian.hom =
      (eqToIso (congrArg (fun b => (Over.pullback b).obj A.abelian.scheme) w.symm)).hom ≫
        e.abelian.hom ≫ (eqToIso (congrArg (fun b => (Over.pullback b).obj B.abelian.scheme) w)).hom := by
  subst h
  change e.abelian.hom = 𝟙 _ ≫ e.abelian.hom ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli
