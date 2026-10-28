import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Presheaf Refined -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology

noncomputable section

/-! The refinement part of a geometric homotopy square commutes
with the original presheaf Cech total cohomology maps in all degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v s t a b
variable (R : Type u) [CommRing R]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {D : Type a} [Category.{b} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

def pullback : (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ (Cᵒᵖ ⥤ ModuleCat.{max u v} R) :=
  NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback F

instance pullback_additive : (pullback R F).Additive := by
  dsimp only [pullback]
  infer_instance

local notation "H" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback R F
local notation "EU" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "EV" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve V

def total (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  ((TotalQuasiIso.CechTotalQuasiIso.bicomplex R EU).obj K).total (.up ℕ)

def map {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) :
    CechPresheafRefinedCohomology.total R U K ⟶ CechPresheafRefinedCohomology.total R U L := TotalQuasiIso.CechTotalQuasiIso.map R EU f

def refinement (K : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) : CechPresheafRefinedCohomology.total R V K ⟶
    CechPresheafRefinedCohomology.total R U (((H).mapHomologicalComplex (.up ℕ)).obj K) :=
  NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r K

def cohomology (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) (q : ℕ) : ModuleCat.{max u v} R :=
  (CechPresheafRefinedCohomology.total R U K).homology q

def mapCohomology {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) (q : ℕ) :
    cohomology R U K q ⟶ cohomology R U L q := HomologicalComplex.homologyMap (CechPresheafRefinedCohomology.map R U f) q

def refinementCohomology (K : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) (q : ℕ) : cohomology R V K q ⟶
    cohomology R U (((H).mapHomologicalComplex (.up ℕ)).obj K) q :=
  HomologicalComplex.homologyMap (refinement R F U V r K) q

variable {K L : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (f : K ⟶ L)

omit [Quiver.IsThin D] in
theorem source_coordinates : HomologicalComplex₂.total.map
    ((NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.source V).map f) (.up ℕ) = CechPresheafRefinedCohomology.map R V f := rfl

omit [Quiver.IsThin D] [HasBinaryProducts D]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F] in
theorem target_coordinates : HomologicalComplex₂.total.map
    ((NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.target F U).map f) (.up ℕ) =
      CechPresheafRefinedCohomology.map R U (((H).mapHomologicalComplex (.up ℕ)).map f) := rfl

theorem refinement_naturality : CechPresheafRefinedCohomology.map R V f ≫ refinement R F U V r L =
    refinement R F U V r K ≫ CechPresheafRefinedCohomology.map R U (((H).mapHomologicalComplex (.up ℕ)).map f) :=
  (congrArg (fun q => q ≫ NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r L)
    (source_coordinates R V f).symm).trans
      ((NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.naturality F U V r f).trans
        (congrArg (fun q => NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r K ≫ q)
          (target_coordinates R F U f)))

theorem refinement_homology (q : ℕ) : mapCohomology R V f q ≫ refinementCohomology R F U V r L q =
    refinementCohomology R F U V r K q ≫ mapCohomology R U (((H).mapHomologicalComplex (.up ℕ)).map f) q :=
  (HomologicalComplex.homologyMap_comp _ _ q).symm.trans
    ((congrArg (fun a => HomologicalComplex.homologyMap a q)
      (refinement_naturality R F U V r f)).trans (HomologicalComplex.homologyMap_comp _ _ q))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology
