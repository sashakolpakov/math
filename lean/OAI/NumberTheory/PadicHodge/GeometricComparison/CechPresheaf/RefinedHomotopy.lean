import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalHomotopySquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Refined Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy

noncomputable section

/-! The refinement part of a geometric homotopy square commutes
with the original presheaf Cech total H-one maps. -/

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
  NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback F

instance pullback_additive : (pullback R F).Additive := by
  dsimp only [pullback]
  infer_instance

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.pullback R F
local notation "EU" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "EV" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve V

def total (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  ((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex R EU).obj K).total (.up ℕ)

def map {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) :
    CechPresheafRefinedHomotopy.total R U K ⟶ CechPresheafRefinedHomotopy.total R U L := Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map R EU f

def refinement (K : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) : CechPresheafRefinedHomotopy.total R V K ⟶
    CechPresheafRefinedHomotopy.total R U (((H).mapHomologicalComplex (.up ℕ)).obj K) :=
  RefinedReindex.CechPresheafRefinedReindex.map F U V r K

def hOne (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) : ModuleCat.{max u v} R :=
  (CechPresheafRefinedHomotopy.total R U K).homology 1

def mapHOne {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) :
    hOne R U K ⟶ hOne R U L := HomologicalComplex.homologyMap (CechPresheafRefinedHomotopy.map R U f) 1

def refinementHOne (K : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) : hOne R V K ⟶
    hOne R U (((H).mapHomologicalComplex (.up ℕ)).obj K) :=
  HomologicalComplex.homologyMap (refinement R F U V r K) 1

variable {K L : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (f : K ⟶ L)

omit [Quiver.IsThin D] in
theorem source_coordinates : HomologicalComplex₂.total.map
    ((RefinedReindex.CechPresheafRefinedReindex.source V).map f) (.up ℕ) = CechPresheafRefinedHomotopy.map R V f := rfl

omit [Quiver.IsThin D] [HasBinaryProducts D]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F] in
theorem target_coordinates : HomologicalComplex₂.total.map
    ((RefinedReindex.CechPresheafRefinedReindex.target F U).map f) (.up ℕ) =
      CechPresheafRefinedHomotopy.map R U (((H).mapHomologicalComplex (.up ℕ)).map f) := rfl

theorem refinement_naturality : CechPresheafRefinedHomotopy.map R V f ≫ refinement R F U V r L =
    refinement R F U V r K ≫ CechPresheafRefinedHomotopy.map R U (((H).mapHomologicalComplex (.up ℕ)).map f) :=
  (congrArg (fun q => q ≫ RefinedReindex.CechPresheafRefinedReindex.map F U V r L)
    (source_coordinates R V f).symm).trans
      ((RefinedReindex.CechPresheafRefinedReindex.naturality F U V r f).trans
        (congrArg (fun q => RefinedReindex.CechPresheafRefinedReindex.map F U V r K ≫ q)
          (target_coordinates R F U f)))

theorem refinement_homology : mapHOne R V f ≫ refinementHOne R F U V r L =
    refinementHOne R F U V r K ≫ mapHOne R U (((H).mapHomologicalComplex (.up ℕ)).map f) :=
  (HomologicalComplex.homologyMap_comp _ _ 1).symm.trans
    ((congrArg (fun q => HomologicalComplex.homologyMap q 1)
      (refinement_naturality R F U V r f)).trans (HomologicalComplex.homologyMap_comp _ _ 1))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy
