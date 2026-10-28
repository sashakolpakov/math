import OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveBicomplex

/-! # Cochain Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.CochainExact

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! Exactness of Čech cochains from exactness on their tuple intersections. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- Degree `p` of the native Čech-complex functor on sheaves. -/
def cechCochainFunctor (p : ℕ) :
    Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U ⋙ HomologicalComplex.eval _ (.up ℕ) p

instance cechCochainFunctor_preservesZero (p : ℕ) :
    (cechCochainFunctor U p).PreservesZeroMorphisms where
  map_zero F G := by
    change ((InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (0 : F ⟶ G)).f p = 0
    rw [Functor.map_zero]
    rfl

/-- A native cochain map acts on each tuple by the given morphism of sections. -/
theorem cechCochainFunctor_map_apply {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (p : ℕ) (x : (cechCochainFunctor U p).obj F)
    (i : Fin (p + 1) → ι) :
    Cochains.TopologicalSpace.cechCochainAddEquiv G.obj U p ((cechCochainFunctor U p).map f x) i =
      f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k)))
        (Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U p x i) := by
  rw [Cochains.TopologicalSpace.cechCochainAddEquiv_apply, Cochains.TopologicalSpace.cechCochainAddEquiv_apply]
  exact ConcreteCategory.congr_hom
    (Pi.map_π (fun j : Fin (p + 1) → ι =>
      f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (j k)))) i) x

/-- Products of exact section sequences give an exact sequence of native Čech cochains. -/
theorem cechCochainFunctor_exact_of_sections
    (S : ShortComplex (Sheaf AddCommGrpCat.{u} X)) (p : ℕ)
    (hsections : ∀ (i : Fin (p + 1) → ι)
      (x : S.X₂.obj.obj (op (∏ᶜ fun k : Fin (p + 1) => U (i k)))),
      S.g.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k))) x = 0 →
      ∃ y : S.X₁.obj.obj (op (∏ᶜ fun k : Fin (p + 1) => U (i k))),
        S.f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k))) y = x) :
    (S.map (cechCochainFunctor U p)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  have hi (i : Fin (p + 1) → ι) :
      S.g.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k)))
        (Cochains.TopologicalSpace.cechCochainAddEquiv S.X₂.obj U p x i) = 0 := by
    have h := congrArg (fun z => Cochains.TopologicalSpace.cechCochainAddEquiv S.X₃.obj U p z i) hx
    change Cochains.TopologicalSpace.cechCochainAddEquiv S.X₃.obj U p
      ((cechCochainFunctor U p).map S.g x) i = _ at h
    rw [cechCochainFunctor_map_apply, map_zero, Pi.zero_apply] at h
    exact h
  choose y hy using fun i => hsections i (Cochains.TopologicalSpace.cechCochainAddEquiv S.X₂.obj U p x i) (hi i)
  let y' := (Cochains.TopologicalSpace.cechCochainAddEquiv S.X₁.obj U p).symm y
  refine ⟨y', ?_⟩
  apply (Cochains.TopologicalSpace.cechCochainAddEquiv S.X₂.obj U p).injective
  funext i
  change Cochains.TopologicalSpace.cechCochainAddEquiv S.X₂.obj U p
    ((cechCochainFunctor U p).map S.f y') i = _
  rw [cechCochainFunctor_map_apply]
  have hy' : Cochains.TopologicalSpace.cechCochainAddEquiv S.X₁.obj U p y' = y := AddEquiv.apply_symm_apply _ _
  rw [hy']
  exact hy i

end TopCat.Sheaf

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.CochainExact
