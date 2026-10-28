import OAI.AlgebraicGeometry.Picard.PoincareBundle.FaithfulPullback

/-! # Descent Uniqueness -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.DescentUniqueness

noncomputable section

/-!
# Effective and unique geometric line-bundle descent for PoincareBundle

The canonical invariant construction recovers the full supplied coaction.
Its adjunction unit is an isomorphism on line bundles, giving uniqueness
with the geometric descent datum retained.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Comonad

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]

/-- The canonical recovery isomorphism respects the entire geometric coaction. -/
def descendedDatumIso (D : BeckDescent.SheafDatum f) (hD : Bundles.IsLine D.A) :
    (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)).obj
      (GlobalLineDescent.descendedLineBundle f D hD).sheaf ≅ D := by
  let a := BeckDescent.invariantComparison f D
  have ha : IsIso a.f := GlobalLineDescent.invariantComparison_isIso f D hD
  have hm : IsIso ((Comonad.forget
      (Scheme.Modules.pullbackPushforwardAdjunction f).toComonad).map a) := ha
  have hi : IsIso a := isIso_of_reflects_iso a
    (Comonad.forget (Scheme.Modules.pullbackPushforwardAdjunction f).toComonad)
  exact @asIso _ _ _ _ a hi

/-- The adjunction unit recovers a line bundle from its canonical pullback datum. -/
theorem unit_isIso (M : Y.Modules) (hM : Bundles.IsLine M) :
    IsIso ((ComonadicityInternal.comparisonAdjunction
      (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app M) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let cadj := ComonadicityInternal.comparisonAdjunction adj
  let D := (Comonad.comparison adj).obj M
  have hD : Bundles.IsLine D.A := hM.pullback f
  have hc : IsIso (cadj.counit.app D).f :=
    GlobalLineDescent.invariantComparison_isIso f D hD
  have htri : (Scheme.Modules.pullback f).map (cadj.unit.app M) ≫
      (cadj.counit.app D).f = 𝟙 _ :=
    congrArg (fun a => a.f) (cadj.left_triangle_components M)
  have hcomp : IsIso ((Scheme.Modules.pullback f).map (cadj.unit.app M) ≫
      (cadj.counit.app D).f) := by
    rw [htri]
    exact (Iso.refl ((Scheme.Modules.pullback f).obj M)).isIso_hom
  have hp : IsIso ((Scheme.Modules.pullback f).map (cadj.unit.app M)) :=
    (@isIso_comp_right_iff _ _ _ _ _ _ _ hc).mp hcomp
  exact FaithfulPullback.isIso_of_pullback f (cadj.unit.app M) hM
    (GlobalLineDescent.invariantSheaf_isLine f D hD) hp

/-- The original line bundle agrees with the invariants of its canonical datum. -/
def unitIso (M : Y.Modules) (hM : Bundles.IsLine M) :
    M ≅ BeckDescent.invariantSheaf f
      ((Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)).obj M) := by
  let a := (ComonadicityInternal.comparisonAdjunction
    (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app M
  have ha : IsIso a := unit_isIso f M hM
  exact @asIso _ _ _ _ a ha

/-- A line bundle descending the supplied full geometric datum is uniquely
isomorphic to the canonical invariant line bundle. -/
def descendedLineBundleUniqueIso
    (D : BeckDescent.SheafDatum f) (hD : Bundles.IsLine D.A)
    (M : Bundles.LineBundle Y)
    (e : (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)).obj M.sheaf ≅ D) :
    M.sheaf ≅ (GlobalLineDescent.descendedLineBundle f D hD).sheaf :=
  unitIso f M.sheaf M.isLine ≪≫
    (ComonadicityInternal.rightAdjointComparison
      (Scheme.Modules.pullbackPushforwardAdjunction f)).mapIso e

/-- A morphism compatible with the pullback coactions comes from exactly
one morphism of the descended line bundles. -/
theorem existsUnique_compatibleHom (M N : Bundles.LineBundle Y)
    (b : (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)).obj M.sheaf ⟶
      (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)).obj N.sheaf) :
    ∃! a : M.sheaf ⟶ N.sheaf,
      (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)).map a = b := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let cadj := ComonadicityInternal.comparisonAdjunction adj
  let η := cadj.unit.app N.sheaf
  have hη : IsIso η := unit_isIso f N.sheaf N.isLine
  let a : M.sheaf ⟶ N.sheaf :=
    (cadj.homEquiv _ _) b ≫ inv η
  have hmap (c : M.sheaf ⟶ N.sheaf) :
      (cadj.homEquiv _ _) ((Comonad.comparison adj).map c) = c ≫ η := by
    rw [Adjunction.homEquiv_unit]
    exact (cadj.unit.naturality c).symm
  have ha : (Comonad.comparison adj).map a = b := by
    apply (cadj.homEquiv _ _).injective
    rw [hmap]
    dsimp [a]
    simp
    rfl
  refine ⟨a, ha, ?_⟩
  intro c hc
  apply (cancel_mono η).mp
  rw [← hmap, hc, ← hmap, ha]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.DescentUniqueness
