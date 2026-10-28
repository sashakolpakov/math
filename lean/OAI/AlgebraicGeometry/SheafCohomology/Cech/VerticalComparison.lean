import OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveResolutionSections
import OAI.AlgebraicGeometry.SheafCohomology.Cech.CochainExact
import OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveAugmentation
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalComparison

/-! # Vertical Comparison -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! The all-degree vertical Čech comparison for covers with acyclic intersections. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- Every nonempty tuple intersection is acyclic in positive sheaf cohomology. -/
def CechIntersectionsAcyclic (F : Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ (p : ℕ) (i : Fin (p + 1) → ι) (q : ℕ),
    Subsingleton (CategoryTheory.Sheaf.H
      ((TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat
        (∏ᶜ fun k : Fin (p + 1) => U (i k)).isOpenEmbedding).obj F) (q + 1))

/-- Acyclic tuple intersections make all positive resolution columns exact. -/
theorem cechInjectiveResolution_columnsExact (F : Sheaf AddCommGrpCat.{u} X)
    (hH : CechIntersectionsAcyclic U F) :
    ComplexUpNatNormalize.Projective.RowsExact (InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F).flip := by
  intro p q
  let I := injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)
  let S := AcyclicResolution.Projective.resolutionDifferentialShortComplex I.cocomplex q
  change (S.map (CochainExact.TopCat.Sheaf.cechCochainFunctor U p)).Exact
  apply CochainExact.TopCat.Sheaf.cechCochainFunctor_exact_of_sections
  intro i x hx
  exact InjectiveResolutionSections.TopCat.Sheaf.injectiveResolution_sections_exact_succ F _ (hH p i) q x hx

/-- The actual vertical edge is a quasi-isomorphism in every positive degree
when all tuple intersections are acyclic. -/
theorem cechInjectiveResolutionVerticalEdge_quasiIsoAt_succ
    (F : Sheaf AddCommGrpCat.{u} X) (hH : CechIntersectionsAcyclic U F) (n : ℕ) :
    QuasiIsoAt (InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U F) (n + 1) := by
  let I := injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)
  apply UpNatVerticalComparison.Projective.vertical_edge_quasiIsoAt
  · intro p
    let S : ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
      ShortComplex.mk (I.ι.f 0) (I.cocomplex.d 0 1) I.ι_f_zero_comp_complex_d
    change (S.map (CochainExact.TopCat.Sheaf.cechCochainFunctor U p)).Exact
    apply CochainExact.TopCat.Sheaf.cechCochainFunctor_exact_of_sections
    intro i x hx
    exact Sheaf.sections_exact_of_left_exact I.exact₀ (inferInstance : Mono S.f) x hx
  · intro p
    change Mono (Limits.Pi.map (fun i : Fin (p + 1) → ι =>
      (I.ι.f 0).hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (i k)))))
    infer_instance
  · exact cechInjectiveResolution_columnsExact U F hH

end TopCat.Sheaf

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison
