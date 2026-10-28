import OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackTripleComparison

/-! # Pullback Equality Comparisons -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackEqualityComparisons

noncomputable section

/-! Equality transports for actual module pullback are compatible with
composition comparisons on either side of a commuting square. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

@[reassoc]
theorem pullbackCongr_trans {X Y : Scheme.{u}} {f g h : X ⟶ Y} (p : f = g) (q : g = h)
    (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr p).hom.app M ≫ (Scheme.Modules.pullbackCongr q).hom.app M =
      (Scheme.Modules.pullbackCongr (p.trans q)).hom.app M := by
  subst g
  subst h
  simp [Scheme.Modules.pullbackCongr]

@[reassoc]
theorem pullbackComp_congr_left {X Y Z : Scheme.{u}} {f f' : X ⟶ Y} (p : f = f')
    (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackCongr p).hom.app ((Scheme.Modules.pullback g).obj M) ≫
      (Scheme.Modules.pullbackComp f' g).hom.app M =
    (Scheme.Modules.pullbackComp f g).hom.app M ≫
      (Scheme.Modules.pullbackCongr (congrArg (fun z => z ≫ g) p)).hom.app M := by
  subst f'
  simp [Scheme.Modules.pullbackCongr]

@[reassoc]
theorem pullbackComp_congr_right {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g g' : Y ⟶ Z}
    (p : g = g') (M : Z.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr p).hom.app M) ≫
      (Scheme.Modules.pullbackComp f g').hom.app M =
    (Scheme.Modules.pullbackComp f g).hom.app M ≫
      (Scheme.Modules.pullbackCongr (congrArg (fun z => f ≫ z) p)).hom.app M := by
  subst g'
  simp [Scheme.Modules.pullbackCongr]

@[reassoc]
theorem pullbackComp_three_forward {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : T.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M =
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app M := by
  have he := congrArg (fun z => z ≫ (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app M)
    (PullbackTripleComparison.Construction.pullbackComp_three f g h M)
  have hi : (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app M = 𝟙 _ := by
    rw [pullbackCongr_trans]
    rfl
  simpa only [Category.assoc, hi, Category.comp_id] using he

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackEqualityComparisons
