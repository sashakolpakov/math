import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveBicomplex

/-! # Cochain Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.CochainExactness.IntrinsicCech

noncomputable section

/-! Exactness of Čech cochains from exactness on their tuple intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- Degree `p` of the native Čech-complex functor on sheaves. -/
def cechCochainFunctor (p : ℕ) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  InjectiveBicomplex.IntrinsicCech.cechSheafComplexFunctor U ⋙ HomologicalComplex.eval _ (.up ℕ) p

instance cechCochainFunctor_preservesZero (p : ℕ) :
    (cechCochainFunctor U p).PreservesZeroMorphisms where
  map_zero F G := by
    change ((InjectiveBicomplex.IntrinsicCech.cechSheafComplexFunctor U).map (0 : F ⟶ G)).f p = 0
    rw [Functor.map_zero]
    rfl

/-- A native cochain map acts on each tuple by the given morphism of sections. -/
theorem cechCochainFunctor_map_apply {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (p : ℕ) (x : (cechCochainFunctor U p).obj F)
    (i : Fin (p + 1) → ι) :
    IntrinsicCech.Cochains.cechCochainAddEquiv G.obj U p ((cechCochainFunctor U p).map f x) i =
      f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k)))
        (IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U p x i) := by
  let x' : ((cechComplexFunctor U).obj F.obj).X p := x
  have hleft := IntrinsicCech.Cochains.cechCochainAddEquiv_apply G.obj U p
    (((cechComplexFunctor U).map f.hom).f p x') i
  have hright := congrArg (f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k))))
    (IntrinsicCech.Cochains.cechCochainAddEquiv_apply F.obj U p x' i)
  have hmap := ConcreteCategory.congr_hom
    (Pi.map_π (fun j : Fin (p + 1) → ι =>
      f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (j k)))) i) x'
  exact hleft.trans (hmap.trans hright.symm)

/-- Products of exact section sequences give an exact sequence of native Čech cochains. -/
theorem cechCochainFunctor_exact_of_sections
    (S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) (p : ℕ)
    (hsections : ∀ (i : Fin (p + 1) → ι)
      (x : S.X₂.obj.obj (op (∏ᶜ fun k : Fin (p + 1) => U (i k)))),
      S.g.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k))) x = 0 →
      ∃ y : S.X₁.obj.obj (op (∏ᶜ fun k : Fin (p + 1) => U (i k))),
        S.f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k))) y = x) :
    (S.map (cechCochainFunctor U p)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  let x' : (cechCochainFunctor U p).obj S.X₂ := x
  have hx' : (cechCochainFunctor U p).map S.g x' = 0 := hx
  have hi (i : Fin (p + 1) → ι) :
      S.g.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k)))
        (IntrinsicCech.Cochains.cechCochainAddEquiv S.X₂.obj U p x' i) = 0 := by
    have h := congrArg (fun z : (cechCochainFunctor U p).obj S.X₃ =>
      IntrinsicCech.Cochains.cechCochainAddEquiv S.X₃.obj U p z i) hx'
    have hz := congrFun (IntrinsicCech.Cochains.cechCochainAddEquiv S.X₃.obj U p).map_zero i
    exact (cechCochainFunctor_map_apply U S.g p x' i).symm.trans (h.trans hz)
  choose y hy using fun i => hsections i (IntrinsicCech.Cochains.cechCochainAddEquiv S.X₂.obj U p x' i) (hi i)
  let y' : (cechCochainFunctor U p).obj S.X₁ := (IntrinsicCech.Cochains.cechCochainAddEquiv S.X₁.obj U p).symm y
  refine ⟨y', ?_⟩
  apply (IntrinsicCech.Cochains.cechCochainAddEquiv S.X₂.obj U p).injective
  funext i
  change IntrinsicCech.Cochains.cechCochainAddEquiv S.X₂.obj U p
    ((cechCochainFunctor U p).map S.f y') i = _
  have hy' : IntrinsicCech.Cochains.cechCochainAddEquiv S.X₁.obj U p y' = y := AddEquiv.apply_symm_apply _ _
  exact (cechCochainFunctor_map_apply U S.f p y' i).trans
    ((congrArg (S.f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k))))
      (congrFun hy' i)).trans (hy i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.CochainExactness.IntrinsicCech
