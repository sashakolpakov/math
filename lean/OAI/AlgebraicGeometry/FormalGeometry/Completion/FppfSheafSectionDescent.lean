import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

/-! # Fppf Sheaf Section Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfSheafSectionDescent

noncomputable section

/-! Compatible sections of any fppf sheaf descend along an actual
flat surjective morphism of finite presentation over the base. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite

namespace Construction

universe u w
variable {S : Scheme.{u}} {X Y : Over S} (q : X ⟶ Y)
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

theorem fppfSingleton_cover :
    Sieve.generate (Presieve.singleton q) ∈ (Scheme.fppfTopology.over S) Y := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
  erw [← Sieve.arrows_generate_map_eq_functorPushforward, Presieve.map_singleton,
    Sieve.generate_sieve]
  exact Precoverage.generate_mem_toGrothendieck q.left.singleton_mem_fppfPrecoverage

theorem fppfSheaf_descend_section (F : Sheaf (Scheme.fppfTopology.over S) (Type w))
    (s : F.obj.obj (op X))
    (hs : ∀ {T : Over S} (a b : T ⟶ X), a ≫ q = b ≫ q →
      F.obj.map a.op s = F.obj.map b.op s) :
    ∃! t : F.obj.obj (op Y), F.obj.map q.op t = s := by
  have hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  exact Presieve.isSheafFor_singleton.mp
    (hF.isSheafFor (Presieve.singleton q) (fppfSingleton_cover q)) s hs

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfSheafSectionDescent
