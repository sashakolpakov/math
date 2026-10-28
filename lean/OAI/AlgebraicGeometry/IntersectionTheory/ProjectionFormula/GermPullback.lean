import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FormStalkComparison

/-! # Germ Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GermPullback

noncomputable section

/-! Germ pullback along a morphism can be computed on any smaller
source open. This avoids imposing equalities of chosen neighborhoods. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) (a : Γ(Y, U)) :
    f.stalkMap x (Y.presheaf.germ U (f x) (hVU hx) a) =
      X.presheaf.germ V x hx (f.appLE U V hVU a) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  change X.presheaf.germ (f ⁻¹ᵁ U) x (hVU hx) (f.app U a) =
    X.presheaf.germ V x hx (X.presheaf.map (homOfLE hVU).op (f.app U a))
  exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) x hx (f.app U a)).symm

def fraction {X : Scheme} (n : ℕ) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (x : X)
    (a s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hs : s.val ∉ (f x).asHomogeneousIdeal) : X.presheaf.stalk x :=
  f.stalkMap x (Projective.PointJets.StalkFractions.fraction n (f x) a s hs)

theorem fraction_congr {X : Scheme} (n : ℕ) (f g : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (he : f = g)
    (x : X) (a s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hf : s.val ∉ (f x).asHomogeneousIdeal)
    (hg : s.val ∉ (g x).asHomogeneousIdeal) :
    fraction n f x a s hf = fraction n g x a s hg := by
  subst g
  rfl

theorem fraction_comp {X Y : Scheme} (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (x : X) (a s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hs : s.val ∉ (g (f x)).asHomogeneousIdeal) :
    fraction n (f ≫ g) x a s hs = f.stalkMap x (fraction n g (f x) a s hs) := by
  change (f ≫ g).stalkMap x _ = _
  rw [Scheme.Hom.stalkMap_comp]
  rfl

theorem fraction_point {X : Scheme} (n : ℕ) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (x y : X) (he : x = y) (a s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hx : s.val ∉ (f x).asHomogeneousIdeal) (hy : s.val ∉ (f y).asHomogeneousIdeal) :
    (X.presheaf.stalkCongr (.of_eq he)).hom (fraction n f x a s hx) = fraction n f y a s hy := by
  subst y
  simp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GermPullback
