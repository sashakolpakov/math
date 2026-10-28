import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Functor

/-! # Stalk Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.StalkQuasiIso.Cech

noncomputable section

/-! Stalks detect quasi-isomorphisms of actual complexes of additive sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

variable {X : TopCat.{0}} {κ : Type*} {c : ComplexShape κ}
  {K L : HomologicalComplex (TopCat.Sheaf AddCommGrpCat.{0} X) c} (f : K ⟶ L) (n : κ)

theorem sheafQuasiIsoAt_iff_stalk :
    QuasiIsoAt f n ↔ ∀ x : X,
      QuasiIsoAt (((TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapHomologicalComplex c).map f) n := by
  constructor
  · intro h x
    have := h
    infer_instance
  · intro h
    rw [quasiIsoAt_iff_isIso_homologyMap, TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    let F := TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x
    let φ := (shortComplexFunctor (TopCat.Sheaf AddCommGrpCat X) c n).map f
    have hφ : ShortComplex.QuasiIso (F.mapShortComplex.map φ) :=
      (quasiIsoAt_iff _ n).mp (h x)
    exact ((MorphismProperty.isomorphisms AddCommGrpCat).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso (ShortComplex.homologyFunctorIso F)).app
        (Arrow.mk φ))).mp ((ShortComplex.quasiIso_iff _).mp hφ)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.StalkQuasiIso.Cech
