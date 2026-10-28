import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Module Locality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleLocality

noncomputable section

/-!
# Localization of module-sheaf descent for PoincareBundle

Restriction to an open subscheme preserves finite limits, hence the
equalizers used to define invariant sheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Geometric restriction preserves finite limits of module sheaves. -/
theorem restrict_preservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  let G : TopCat.Presheaf AddCommGrpCat.{u} Y ⥤ TopCat.Presheaf AddCommGrpCat.{u} X :=
    (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op
  have : PreservesFiniteLimits G := by
    constructor
    intro J _ _
    exact whiskeringLeft_preservesLimitsOfShape J f.opensFunctor.op
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f ⋙
      Scheme.Modules.toPresheaf X) :=
    comp_preservesFiniteLimits (Scheme.Modules.toPresheaf Y) G
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Scheme.Modules.restrictFunctor f) (Scheme.Modules.toPresheaf X)

/-- Open-immersion pullback preserves finite limits. -/
theorem pullback_preservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.pullback f) := by
  have := restrict_preservesFiniteLimits f
  exact preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback f)

/-- The invariant equalizer commutes with restriction to an open subscheme. -/
def restrictEqualizerIso {M N : Y.Modules} (a b : M ⟶ N) :
    (Scheme.Modules.restrictFunctor f).obj (equalizer a b) ≅
      equalizer ((Scheme.Modules.restrictFunctor f).map a)
        ((Scheme.Modules.restrictFunctor f).map b) := by
  have := restrict_preservesFiniteLimits f
  exact PreservesEqualizer.iso (Scheme.Modules.restrictFunctor f) a b

variable {f}

/-- A morphism of module sheaves is an isomorphism if it is an isomorphism
on some open neighborhood of every point. -/
theorem isIso_of_locally_isIso {M N : Y.Modules} (a : M ⟶ N)
    (h : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map a)) : IsIso a := by
  let b : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} Y) ⟶
      (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} Y) := ⟨a.mapPresheaf⟩
  have hb : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map b.hom) := by
    intro y
    obtain ⟨U, hy, ha⟩ := h y
    let z : U := ⟨y, hy⟩
    have hlocal : IsIso (((Scheme.Modules.restrictFunctor U.ι) ⋙
        Scheme.Modules.toPresheaf U ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map a) :=
      @Functor.map_isIso _ _ _ _ _ _
        (Scheme.Modules.toPresheaf U ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z)
        ((Scheme.Modules.restrictFunctor U.ι).map a) ha
    exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι z) a).mp hlocal
  have hbIso : IsIso b := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso b
  have : IsIso ((Scheme.Modules.toPresheaf Y).map a) :=
    @Functor.map_isIso _ _ _ _ _ _ (TopCat.Sheaf.forget AddCommGrpCat.{u} Y) b hbIso
  exact isIso_of_reflects_iso a (Scheme.Modules.toPresheaf Y)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleLocality
