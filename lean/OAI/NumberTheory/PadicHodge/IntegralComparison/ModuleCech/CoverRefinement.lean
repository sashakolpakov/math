import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinementCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.Cover
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Cover Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinement

noncomputable section

/-! The literal refinement map on module-valued affine Čech
cochains induces the canonical change-of-cover isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (M : X.left.Modules)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R
local notation "P" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomologyPresheaf.functor R X) M

def map : DimensionBound.complex R X M U ⟶
    DimensionBound.complex R X M V :=
  GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r P

theorem forget_natural :
    ((G).mapHomologicalComplex (.up ℕ)).map (CoverRefinement.map R X U V r M) ≫
      (DimensionBound.forgetIso R X M V).hom =
    (DimensionBound.forgetIso R X M U).hom ≫
      Cech.CoverRefinement.map U V r M.presheaf := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (G).map ((CoverRefinement.map R X U V r M).f n) ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk κ V).cech P).hom.f n =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech P).hom.f n ≫
      (Cech.CoverRefinement.map U V r M.presheaf).f n
  rw [AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f, AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f]
  let En := (FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)
  let Em := (FormalCoproduct.mk κ V).cech.obj (op ⦋n⦌)
  let a := (FormalCoproduct.cechFunctor.map r).app (op ⦋n⦌)
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.piComparison_natural G
    (fun i : En.I => (P).obj (op (En.obj i)))
    (fun i : Em.I => (P).obj (op (Em.obj i))) a.f (fun i => (P).map (a.φ i).op)

theorem forget_homology_natural (n : ℕ) :
    (G).map (HomologicalComplex.homologyMap (CoverRefinement.map R X U V r M) n) ≫
      (CohomologyNaturality.forgetHomologyIso R X V M n).hom =
    (CohomologyNaturality.forgetHomologyIso R X U M n).hom ≫
      HomologicalComplex.homologyMap (Cech.CoverRefinement.map U V r M.presheaf) n :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.naturality G (.up ℕ)
    (DimensionBound.forgetIso R X M U)
    (DimensionBound.forgetIso R X M V)
    (CoverRefinement.map R X U V r M) (Cech.CoverRefinement.map U V r M.presheaf)
    (forget_natural R X U V r M) n

variable [X.left.IsSeparated] [M.IsQuasicoherent]
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))

theorem cohomology (n : ℕ) :
    (G).map (HomologicalComplex.homologyMap (CoverRefinement.map R X U V r M) (n + 1)) ≫
      (DimensionBound.cohomologyIso R X M V hV haV n).hom =
    (DimensionBound.cohomologyIso R X M U hU haU n).hom := by
  have h := Cech.CoverRefinementCohomology.cohomology U V r
    ((SheafOfModules.toSheaf X.left.ringCatSheaf).obj M) hU hV
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic M U haU)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic M V haV) n
  change (G).map (HomologicalComplex.homologyMap (CoverRefinement.map R X U V r M) (n + 1)) ≫
      ((CohomologyNaturality.forgetHomologyIso R X V M (n + 1)).hom ≫
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechComparison.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso M V hV haV n).hom) =
    (CohomologyNaturality.forgetHomologyIso R X U M (n + 1)).hom ≫
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechComparison.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso M U hU haU n).hom
  rw [← Category.assoc, forget_homology_natural, Category.assoc]
  exact congrArg
    (fun a => (CohomologyNaturality.forgetHomologyIso R X U M (n + 1)).hom ≫ a) h

theorem map_eq_coverIso (n : ℕ) :
    (G).map (HomologicalComplex.homologyMap (CoverRefinement.map R X U V r M) (n + 1)) =
      (Cover.Comparison.iso R X U V hU hV haU haV M n).hom := by
  apply (cancel_mono (DimensionBound.cohomologyIso R X M V hV haV n).hom).mp
  simpa only [Cover.Comparison.iso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      cohomology R X U V r M hU hV haU haV n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinement
