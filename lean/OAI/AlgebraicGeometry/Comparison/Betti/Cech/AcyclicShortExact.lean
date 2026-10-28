import OAI.AlgebraicGeometry.Comparison.Betti.ExtVanishing
import OAI.AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison
import Mathlib.Topology.Sheaves.Abelian

/-! # Acyclic Short Exact -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicShortExact

noncomputable section

/-! Positive cohomology and acyclic Čech intersections pass to cokernels of short exact sequences. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

theorem sheafPositiveCohomology_cokernel {X : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.ShortExact)
    (h₁ : ∀ q : ℕ, Subsingleton (Sheaf.H.{0} S.X₁ (q + 1)))
    (h₂ : ∀ q : ℕ, Subsingleton (Sheaf.H.{0} S.X₂ (q + 1))) :
    ∀ q : ℕ, Subsingleton (Sheaf.H.{0} S.X₃ (q + 1)) := by
  intro q
  let : Abelian (TopCat.Sheaf AddCommGrpCat.{0} X) := inferInstance
  let A : TopCat.Sheaf AddCommGrpCat.{0} X :=
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))
  let : Subsingleton (Abelian.Ext.{0} A S.X₁ (q + 1 + 1)) := h₁ (q + 1)
  let : Subsingleton (Abelian.Ext.{0} A S.X₂ (q + 1)) := h₂ q
  exact ExtVanishing.right_ext_subsingleton.{1, 0, 0} (C := TopCat.Sheaf AddCommGrpCat.{0} X) A hS (q + 1)

theorem cechIntersectionsAcyclic_cokernel {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.ShortExact)
    (h₁ : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U S.X₁)
    (h₂ : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U S.X₂) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U S.X₃ := by
  intro p t q
  let V : Opens X := ∏ᶜ fun k : Fin (p + 1) => U (t k)
  let R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} V.isOpenEmbedding
  let : PreservesFiniteLimits R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict_preservesFiniteLimits V.isOpenEmbedding
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  have hR : (S.map R).ShortExact := hS.map R
  exact sheafPositiveCohomology_cokernel (S.map R) hR (fun r => h₁ p t r) (fun r => h₂ p t r) q

theorem cechIntersectionsAcyclic_of_iso {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (e : F ≅ G)
    (hF : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U G := by
  intro p t q
  let V : Opens X := ∏ᶜ fun k : Fin (p + 1) => U (t k)
  let R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} V.isOpenEmbedding
  let H := Sheaf.functorH.{0} (Opens.grothendieckTopology V) (q + 1)
  let : Subsingleton (H.obj (R.obj F)) := hF p t q
  exact (ConcreteCategory.bijective_of_isIso (H.mapIso (R.mapIso e)).inv).injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicShortExact
