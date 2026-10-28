import OAI.Analysis.DifferentialForms.Manifold.ComplexSheafHomology
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Functor

/-! # Sheaf Stalk Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafStalkQuasiIso.Holomorphic

noncomputable section

/-! Stalks detect quasi-isomorphisms of actual complexes of complex-module sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex

variable {X : TopCat.{0}} {κ : Type*} {c : ComplexShape κ}
  {K L : HomologicalComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{0} ℂ)) c} (f : K ⟶ L) (n : κ)

theorem moduleSheafQuasiIsoAt_of_stalk
    (h : ∀ x : X,
      QuasiIsoAt (((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex c).map f) n) :
    QuasiIsoAt f n := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  erw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro x
  let F := TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X ⋙ TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x
  let φ := (shortComplexFunctor (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{0} ℂ)) c n).map f
  have hφ : ShortComplex.QuasiIso (F.mapShortComplex.map φ) :=
    (quasiIsoAt_iff _ n).mp (h x)
  exact ((MorphismProperty.isomorphisms (ModuleCat.{0} ℂ)).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (ShortComplex.homologyFunctorIso F)).app
      (Arrow.mk φ))).mp ((ShortComplex.quasiIso_iff _).mp hφ)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafStalkQuasiIso.Holomorphic
