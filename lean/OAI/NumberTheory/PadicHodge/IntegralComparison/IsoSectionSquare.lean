import Mathlib.CategoryTheory.Iso

/-! # Iso Section Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IsoSectionSquare

/-! A section comparison square transported through the given chart isomorphisms. -/

open _root_.CategoryTheory

variable {D : Type*} [Category* D] {AU GU AC GC AV GV N U V : D}
  (a : AU ≅ GU) (b : AC ≅ GC) (c : AV ≅ GV)
  (e : AC ⟶ AV) (s : AU ⟶ AC) (r : GU ⟶ N) (q : N ⟶ GC) (t : GC ⟶ GV)
  (u : AU ⟶ U) (v : AV ⟶ V) (w : AC ⟶ V) (k : U ⟶ V)

theorem square (h₁ : a.hom ≫ r ≫ q = s ≫ b.hom)
    (h₂ : b.hom ≫ t = e ≫ c.hom) (h₃ : u ≫ k = s ≫ w) (h₄ : e ≫ v = w) :
    (a.inv ≫ u) ≫ k = r ≫ q ≫ t ≫ c.inv ≫ v := by
  have h₂' : b.hom ≫ t ≫ c.inv ≫ v = e ≫ v := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun z => z ≫ c.inv ≫ v) h₂
  have h' : a.hom ≫ r ≫ q ≫ t ≫ c.inv ≫ v = s ≫ w := by
    calc
      _ = s ≫ b.hom ≫ t ≫ c.inv ≫ v := by
        simpa only [Category.assoc] using congrArg (fun z => z ≫ t ≫ c.inv ≫ v) h₁
      _ = s ≫ w := by rw [h₂', h₄]
  exact (Category.assoc _ _ _).trans (a.inv_comp_eq.mpr (h₃.trans h'.symm))

end OAI.NumberTheory.PadicHodge.IntegralComparison.IsoSectionSquare
