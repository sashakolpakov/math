import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechTotalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechConcentration
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Cech Additive Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic

noncomputable section

/-! The generic additive ordered Čech total is the scalar-forgotten
original base-module total, naturally for every actual coefficient map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

abbrev forgetScalars : ModuleCat.{u} Γ(S, ⊤) ⥤ AddCommGrpCat.{u} := forget₂ _ _

local instance finiteBiproducts : HasFiniteBiproducts (ModuleCat.{u} Γ(S, ⊤)) :=
  Abelian.hasFiniteBiproducts

def totalFunctor : CochainComplex X.Modules ℕ ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  (Relative.AdditiveCechConcentration.presheaves (X := X)).mapHomologicalComplex (.up ℕ) ⋙
    (OrderedCech.Functor.Projection.functor U).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ)

def totalIso (K : CochainComplex X.Modules ℕ) :
    ((forgetScalars (S := S)).mapHomologicalComplex (.up ℕ)).obj
      ((Cech.ConcentrationNaturality.totalFunctor π U).obj K) ≅ (Intrinsic.totalFunctor U).obj K :=
  ((forgetScalars (S := S)).mapHomologicalComplex (.up ℕ)).mapIso
    (CechTotalCoordinates.Intrinsic.iso π U K).symm ≪≫
      OrderedCech.CoefficientTotal.totalIso U (forgetScalars (S := S))
        (RelativeCech.CoefficientQuasiIso.coefficients π K)

theorem inverse_naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) :
    (Cech.ConcentrationNaturality.totalFunctor π U).map a ≫
      (CechTotalCoordinates.Intrinsic.iso π U L).inv =
    (CechTotalCoordinates.Intrinsic.iso π U K).inv ≫
      (CechTotalCoordinates.Intrinsic.sourceFunctor π U).map a := by
  have hn := CechTotalCoordinates.Intrinsic.naturality π U a
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
    using congrArg (fun f => (CechTotalCoordinates.Intrinsic.iso π U K).inv ≫
      f ≫ (CechTotalCoordinates.Intrinsic.iso π U L).inv) hn.symm

abbrev mappedInverse_naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) := by
  let G := (forgetScalars (S := S)).mapHomologicalComplex (.up ℕ)
  have hf := congrArg G.map (inverse_naturality π U a)
  rw [G.map_comp, G.map_comp] at hf
  exact hf

abbrev coefficient_naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) :=
  OrderedCech.CoefficientNaturality.Total.totalIso_naturality U (forgetScalars (S := S))
    (RelativeCech.CoefficientQuasiIso.coefficientMap π a)

theorem totalIso_naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) :
    ((forgetScalars (S := S)).mapHomologicalComplex (.up ℕ)).map
      ((Cech.ConcentrationNaturality.totalFunctor π U).map a) ≫ (totalIso π U L).hom =
    (totalIso π U K).hom ≫ (Intrinsic.totalFunctor U).map a :=
  DualComplexHomology.compose_squares _ _ _ _ _ _ _
    (mappedInverse_naturality π U a) (coefficient_naturality π U a)

def homologyIso (K : CochainComplex X.Modules ℕ) (q : ℕ) :
    (forgetScalars (S := S)).obj (((Cech.ConcentrationNaturality.totalFunctor π U).obj K).homology q) ≅
      ((Intrinsic.totalFunctor U).obj K).homology q :=
  ((((Cech.ConcentrationNaturality.totalFunctor π U).obj K).sc q).mapHomologyIso
    (forgetScalars (S := S))).symm ≪≫ homologyMapIso (totalIso π U K) q

theorem homologyIso_naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) (q : ℕ) :
    (forgetScalars (S := S)).map
      (homologyMap ((Cech.ConcentrationNaturality.totalFunctor π U).map a) q) ≫
        (homologyIso π U L q).hom =
    (homologyIso π U K q).hom ≫ homologyMap ((Intrinsic.totalFunctor U).map a) q :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.naturality (forgetScalars (S := S)) (.up ℕ)
    (totalIso π U K) (totalIso π U L)
    ((Cech.ConcentrationNaturality.totalFunctor π U).map a) ((Intrinsic.totalFunctor U).map a)
    (totalIso_naturality π U a) q

variable [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))

include π hU in
theorem quasiIso {K L : CochainComplex X.Modules ℕ}
    [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
    (a : K ⟶ L) [QuasiIso a] : QuasiIso ((Intrinsic.totalFunctor U).map a) := by
  let : QuasiIso ((Cech.ConcentrationNaturality.totalFunctor π U).map a) :=
    OrderedCech.QuasiIso.quasiIso π U a hU
  have h := totalIso_naturality π U a
  rw [← Iso.inv_comp_eq] at h
  rw [← h]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic
