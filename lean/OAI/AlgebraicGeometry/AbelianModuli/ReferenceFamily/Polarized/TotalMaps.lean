import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Total Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TotalMaps

noncomputable section

/-! Actual maps of total spaces induced by polarized comparisons over
changing bases, with their cartesian square and composition formula. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem totalMap_comparison_composition
    {V₀ V₁ V₂ V₃ V₄ V₅ V₆ : Scheme.{0}}
    (q : V₀ ⟶ V₁) (r : V₁ ⟶ V₂) (c : V₂ ⟶ V₃) (π : V₃ ⟶ V₄)
    (p : V₂ ⟶ V₅) (πf : V₅ ⟶ V₄) (πb : V₁ ⟶ V₆) (a : V₆ ⟶ V₅)
    (hc : c ≫ π = p ≫ πf) (hr : r ≫ p = πb ≫ a) :
    (q ≫ r ≫ c) ≫ π = (q ≫ πb) ≫ (a ≫ πf) := by
  simp only [Category.assoc]
  rw [hc, ← Category.assoc r p πf, hr]
  simp only [Category.assoc]

variable {S T U : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (f : T ⟶ S) (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f))

def polarizedTotalMap : B.abelian.scheme.left ⟶ A.abelian.scheme.left :=
  e.abelian.hom.left ≫ pullback.fst A.abelian.scheme.hom f

theorem polarizedTotalMap_base :
    polarizedTotalMap A B f e ≫ A.abelian.scheme.hom = B.abelian.scheme.hom ≫ f := by
  change (e.abelian.hom.left ≫ pullback.fst A.abelian.scheme.hom f) ≫ A.abelian.scheme.hom = _
  exact (Category.assoc e.abelian.hom.left (pullback.fst A.abelian.scheme.hom f)
    A.abelian.scheme.hom).trans
    ((congrArg (fun q => e.abelian.hom.left ≫ q) (pullback.condition (f := A.abelian.scheme.hom)
      (g := f))).trans
      ((Category.assoc e.abelian.hom.left (pullback.snd A.abelian.scheme.hom f) f).symm.trans
        (congrArg (fun q => q ≫ f) e.abelian.hom.w)))

theorem polarizedTotalMap_isPullback :
    IsPullback (polarizedTotalMap A B f e) B.abelian.scheme.hom A.abelian.scheme.hom f :=
  IsPullback.of_iso_pullback ⟨polarizedTotalMap_base A B f e⟩
    ((Over.forget T).mapIso e.abelian) rfl e.abelian.hom.w

theorem polarizedTotalMap_id :
    polarizedTotalMap A A (𝟙 S) (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A).symm =
      𝟙 A.abelian.scheme.left := by
  change A.abelian.pullbackIdIso.inv.left ≫ pullback.fst A.abelian.scheme.hom (𝟙 S) = _
  rw [← A.abelian.pullbackIdIso_hom_left]
  exact ((Over.forget S).mapIso A.abelian.pullbackIdIso).inv_hom_id

theorem polarizedTotalMap_eq_of_base_eq {f' : T ⟶ S} (h : f = f')
    (d : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f'))
    [Subsingleton (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f))] :
    polarizedTotalMap A B f e = polarizedTotalMap A B f' d := by
  cases h
  exact congrArg (polarizedTotalMap A B f) (Subsingleton.elim e d)

theorem polarizedTotalMap_comp
    (C : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N U)
    (h : U ⟶ T) (d : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso C (B.pullback h)) :
    polarizedTotalMap A C (h ≫ f)
        (d.trans ((e.pullback h).trans (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A f h))) =
      polarizedTotalMap B C h d ≫ polarizedTotalMap A B f e := by
  change (d.abelian.hom.left ≫ ((Over.pullback h).map e.abelian.hom).left ≫
      (A.abelian.pullbackCompIso f h).inv.left) ≫ pullback.fst A.abelian.scheme.hom (h ≫ f) =
    (d.abelian.hom.left ≫ pullback.fst B.abelian.scheme.hom h) ≫
      (e.abelian.hom.left ≫ pullback.fst A.abelian.scheme.hom f)
  exact totalMap_comparison_composition d.abelian.hom.left
    ((Over.pullback h).map e.abelian.hom).left (A.abelian.pullbackCompIso f h).inv.left
    (pullback.fst A.abelian.scheme.hom (h ≫ f))
    (pullback.fst (A.abelian.pullback f).scheme.hom h) (pullback.fst A.abelian.scheme.hom f)
    (pullback.fst B.abelian.scheme.hom h) e.abelian.hom.left
    (A.abelian.pullbackCompIso_inv_left_fst f h) (HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst e.abelian.hom h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TotalMaps
