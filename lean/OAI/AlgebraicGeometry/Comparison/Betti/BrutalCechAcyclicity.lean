import OAI.AlgebraicGeometry.Comparison.Betti.BrutalRelative
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.AdditiveImage
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Cech
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicShortExact

/-! # Brutal Cech Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.BrutalCechAcyclicity.Hodge

noncomputable section

section

/-! The actual direct-image coefficient map restricts to the independent algebraic and holomorphic Hodge truncations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

local instance brutalDirectImageRightAdjoint : (TopologicalSheafPullback.sheafDirectImage f).IsRightAdjoint :=
  (TopologicalSheafPullback.sheafImageAdjunction f).isRightAdjoint

variable {K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ}
  {L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L) (r : ℤ)

def brutalSheafDirectImageMap : Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r ⟶
    ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r) :=
  BrutalRelative.Hodge.brutalRelativeComplexMap (C := ConstantSheafSections.ComplexSheaves Y) (D := ConstantSheafSections.ComplexSheaves X)
    (TopologicalSheafPullback.sheafDirectImage f) α r

theorem brutalSheafDirectImageMap_inclusion :
    brutalSheafDirectImageMap f α r ≫
        ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) =
      Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r ≫ α :=
  BrutalRelative.Hodge.brutalRelativeComplexMap_inclusion (C := ConstantSheafSections.ComplexSheaves Y) (D := ConstantSheafSections.ComplexSheaves X)
    (TopologicalSheafPullback.sheafDirectImage f) α r

local instance brutalDirectImageAbAdditive : (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).Additive where
  map_add := by intros; rfl

theorem brutalSheafDirectImageMap_additiveInclusion :
    Godement.AdditiveImage.additiveGodementComplexMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) ≫ Godement.AdditiveImage.additiveDirectImageComplexMap f α =
      Godement.AdditiveImage.additiveDirectImageComplexMap f (brutalSheafDirectImageMap f α r) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
          (Godement.AdditiveImage.additiveGodementComplexMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r)) :=
  (Godement.AdditiveImage.additiveDirectImageComplexMap_precompose f α (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)).symm.trans
    ((congrArg (Godement.AdditiveImage.additiveDirectImageComplexMap f) (brutalSheafDirectImageMap_inclusion f α r).symm).trans
      (Godement.AdditiveImage.additiveDirectImageComplexMap_postcompose f (brutalSheafDirectImageMap f α r) (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r)))

end

/-! Termwise intersection acyclicity is retained by the independent degree truncation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ) (r : ℤ)
  (hK : ∀ n, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := X) U
    ((Complex.SheafForget.Flasque.sheafForget X).obj (K.X n)))

include hK in
theorem brutalCechIntersectionsAcyclic (n : ℕ) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := X) U
      ((Complex.SheafForget.Flasque.sheafForget X).obj ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).X n)) := by
  by_cases h : r ≤ (n : ℤ)
  · exact Cech.AcyclicShortExact.cechIntersectionsAcyclic_of_iso U
      ((Complex.SheafForget.Flasque.sheafForget X).mapIso (BrutalComplexMap.Hodge.brutalRetainedTermIso K r n h).symm) (hK n)
  · intro p t q
    let V : Opens X := ∏ᶜ fun k : Fin (p + 1) => U (t k)
    have hz : IsZero ((Complex.SheafForget.Flasque.sheafForget X).obj ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).X n)) :=
      (Complex.SheafForget.Flasque.sheafForget X).map_isZero (BrutalComplexMap.Hodge.brutalTerm_isZero K r n h)
    have hR := (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} V.isOpenEmbedding).map_isZero hz
    exact Sheaf.subsingleton_H_of_isZero hR (q + 1)

end

end OAI.AlgebraicGeometry.Comparison.Betti.BrutalCechAcyclicity.Hodge
