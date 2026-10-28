import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafLocalExactness
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Functor

/-! # Sheaf Stalk Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafStalkQuasiIso.ModuleSheafStalkQuasiIso

noncomputable section

/-! Stalks detect quasi-isomorphisms of actual complexes of additive sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

variable (R : Type) [CommRing R] {X : TopCat.{0}} {κ : Type*} {c : ComplexShape κ}
  {K L : HomologicalComplex (TopCat.Sheaf (ModuleCat.{0} R) X) c} (f : K ⟶ L) (n : κ)

theorem sheafQuasiIsoAt_iff_stalk :
    QuasiIsoAt f n ↔ ∀ x : X,
      QuasiIsoAt (((TopCat.Sheaf.forget (ModuleCat R) X ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat R) x).mapHomologicalComplex c).map f) n := by
  constructor
  · intro h x
    have := h
    infer_instance
  · intro h
    rw [quasiIsoAt_iff_isIso_homologyMap, TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    let F := TopCat.Sheaf.forget (ModuleCat R) X ⋙ TopCat.Presheaf.stalkFunctor (ModuleCat R) x
    let φ := (shortComplexFunctor (TopCat.Sheaf (ModuleCat R) X) c n).map f
    have hφ : ShortComplex.QuasiIso (F.mapShortComplex.map φ) :=
      (quasiIsoAt_iff _ n).mp (h x)
    exact ((MorphismProperty.isomorphisms (ModuleCat R)).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso (ShortComplex.homologyFunctorIso F)).app
        (Arrow.mk φ))).mp ((ShortComplex.quasiIso_iff _).mp hφ)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafStalkQuasiIso.ModuleSheafStalkQuasiIso
