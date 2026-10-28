import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Pullback Triple Comparison -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackTripleComparison

noncomputable section

/-! The two actual ways of composing three module pullbacks agree,
with the equality of composite scheme maps made explicit. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

@[reassoc]
theorem pullbackComp_three {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : T.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M =
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M := by
  let a := (Scheme.Modules.pullbackComp f (g ≫ h)).app M
  let b := (Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackComp g h).app M)
  let c := (Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M)
  let d := (Scheme.Modules.pullbackComp (f ≫ g) h).app M
  let e := (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).app M
  have hn := congrArg (fun z => z.app M) (Scheme.Modules.pseudofunctor_associativity f g h)
  change a.inv ≫ b.inv ≫ c.hom ≫ d.hom = e.hom at hn
  have hc := congrArg (fun z => b.hom ≫ a.hom ≫ z) hn
  have hs : c.hom ≫ d.hom = b.hom ≫ a.hom ≫ e.hom := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hc
  exact hs.symm

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackTripleComparison
