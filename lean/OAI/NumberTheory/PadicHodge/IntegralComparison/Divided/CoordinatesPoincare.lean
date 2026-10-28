import OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesDeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.Poincare

/-! # Coordinates Poincare -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesPoincare

noncomputable section

/-!
# IntegralComparison: exactness of the canonical relative divided-coordinate resolution

Evaluation identifies the augmented presheaf complex with the actual
integral Poincaré complex of each crystalline ambient ring. Thus its
canonical augmentation is a quasi-isomorphism on the original site.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (σ : Type u) [Fintype σ]
  (U : BigCrystallineSite.Object p B J δ f)

abbrev evaluation : ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  (CategoryTheory.evaluation _ _).obj (op U)

local notation "ev" => OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesPoincare.evaluation U
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesDeRham.complex (p := p) (B := B) (J := J) (δ := δ) (f := f) σ
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesDeRham.ambientPresheaf (p := p) (B := B) (J := J) (δ := δ) (f := f)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.Poincare.complex U.ring σ U.ideal U.dividedPowers

def evaluationComponentIso (n : ℕ) :
    (((ev).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X n ≅ (P).X n :=
  (AddEquiv.refl (CoordinatesForms.Forms σ U n)).toAddCommGrpIso

omit [Fintype σ] in
theorem evaluation_d (n : ℕ) :
    (((ev).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).d n (n + 1) ≫
        (evaluationComponentIso σ U (n + 1)).hom =
      (evaluationComponentIso σ U n).hom ≫ (P).d n (n + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro ω
  change ((K).d n (n + 1)).app (op U) ω = (P).d n (n + 1) ω
  rw [CoordinatesDeRham.complex_d]
  exact (Additive.Poincare.complex_d_apply U.ring σ U.ideal U.dividedPowers n ω).symm

def evaluationIso : ((ev).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅ P :=
  HomologicalComplex.Hom.isoOfComponents (evaluationComponentIso σ U) (by
    intro n m h
    change n + 1 = m at h
    subst m
    exact (evaluation_d σ U n).symm)

def sourceIso :
    ((ev).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ _).obj A) ≅
      (CochainComplex.single₀ AddCommGrpCat.{u}).obj (AddCommGrpCat.of U.ring) :=
  (HomologicalComplex.singleMapHomologicalComplex ev (ComplexShape.up ℕ) 0).app A

omit [Fintype σ] [Fact p.Prime] in
theorem sourceIso_inv_zero : (sourceIso U).inv.f 0 = 𝟙 (AddCommGrpCat.of U.ring) := by
  exact (HomologicalComplex.singleMapHomologicalComplex_inv_app_self ev (ComplexShape.up ℕ) 0 A).trans
    (by
      simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
      rfl)

abbrev evaluatedAugmentation := ((ev).mapHomologicalComplex (ComplexShape.up ℕ)).map
  (CoordinatesDeRham.augmentation σ)

def transportedAugmentation :
    (CochainComplex.single₀ AddCommGrpCat.{u}).obj (AddCommGrpCat.of U.ring) ⟶ P :=
  (sourceIso U).inv ≫ evaluatedAugmentation σ U ≫ (evaluationIso σ U).hom

omit [Fintype σ] in
theorem transportedAugmentation_zero (a : U.ring) :
    (transportedAugmentation σ U).f 0 a = CoordinatesDeRham.constants σ U a := by
  change (evaluationIso σ U).hom.f 0
    ((evaluatedAugmentation σ U).f 0 ((sourceIso U).inv.f 0 a)) = _
  rw [sourceIso_inv_zero]
  change ((CoordinatesDeRham.augmentation σ).f 0).app (op U) a = _
  rw [CoordinatesDeRham.augmentation_zero]
  rfl

theorem augmentation_comparison : transportedAugmentation σ U =
    Additive.Poincare.augmentation U.ring σ U.ideal U.dividedPowers := by
  apply HomologicalComplex.from_single_hom_ext
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact (transportedAugmentation_zero σ U a).trans
    ((CoordinatesDeRham.constants_symbol σ U a).trans
      (Additive.Poincare.augmentation_zero U.ring σ U.ideal U.dividedPowers a).symm)

instance evaluatedAugmentation_quasiIso : QuasiIso (evaluatedAugmentation σ U) := by
  have h : QuasiIso (transportedAugmentation σ U) := by
    rw [augmentation_comparison]
    infer_instance
  exact (quasiIso_iff_comp_right _ (evaluationIso σ U).hom).mp
    ((quasiIso_iff_comp_left (sourceIso U).inv _).mp h)

/-- The canonical augmented relative form presheaf is exact in every positive degree. -/
instance augmentation_quasiIso :
    QuasiIso (CoordinatesDeRham.augmentation (p := p) (B := B) (J := J) (δ := δ) (f := f) σ) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
  intro U
  exact evaluatedAugmentation_quasiIso σ U.unop

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesPoincare
