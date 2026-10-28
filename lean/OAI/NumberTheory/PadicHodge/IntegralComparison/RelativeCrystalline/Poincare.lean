import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Augmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.Poincare

/-! # Poincare -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Poincare

noncomputable section

/-!
# IntegralComparison: relative Poincaré under actual divided-coordinate identifications

The objectwise identification need only respect the projection to the
original object. No natural choice of divided coordinates is required.
The resulting quasi-isomorphism is the canonical presheaf augmentation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (σ : Type u) (U : C)
  (e : Crystalline.DividedCoordinates.object (Q.obj U) σ ≅ H.obj U)
  (he : e.hom ≫ π.app U = Crystalline.DividedCoordinates.projection (Q.obj U) σ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.ring (Q.obj U)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object (Q.obj U) σ

def freeAlgEquiv :
    letI : Algebra R (H.obj U).ring := FormData.relativeAlgebra H Q π U
    (H.obj U).ring ≃ₐ[R] (G).ring := by
  letI : Algebra R (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact { Crystalline.RelativeIso.ringEquiv e with
    commutes' a := congrArg (fun α : G ⟶ Q.obj U => α.ringMap a) he }

def formsEquiv (n : ℕ) : FormData.Forms H Q π U n ≃+
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R (G).ring (G).ideal (G).dividedPowers n := by
  letI : Algebra R (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv (A := CommAlgCat.of R (H.obj U).ring)
    (B := CommAlgCat.of R (G).ring) (freeAlgEquiv H Q π σ U e he)
    e.hom.ringMap.isDPMorphism e.inv.ringMap.isDPMorphism n).toAddEquiv

theorem formsEquiv_symbol (n : ℕ) (a : (H.obj U).ring) (t : Fin n → (H.obj U).ring) :
    formsEquiv H Q π σ U e he n (FormData.symbol H Q π U n a t) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R (G).ring (G).ideal (G).dividedPowers
        (e.hom.ringMap a) (fun i => e.hom.ringMap (t i)) := by
  let : Algebra R (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (A := CommAlgCat.of R (H.obj U).ring)
    (B := CommAlgCat.of R (G).ring)
    (CommAlgCat.ofHom (freeAlgEquiv H Q π σ U e he).toAlgHom) e.hom.ringMap.isDPMorphism n a t

theorem formsEquiv_differential (n : ℕ) (ω : FormData.Forms H Q π U n) :
    formsEquiv H Q π σ U e he (n + 1)
        (FormMaps.differential H Q π U n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R (G).ring (G).ideal (G).dividedPowers n (formsEquiv H Q π σ U e he n ω) := by
  let : Algebra R (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv_differential (A := CommAlgCat.of R (H.obj U).ring)
    (B := CommAlgCat.of R (G).ring) (freeAlgEquiv H Q π σ U e he)
    e.hom.ringMap.isDPMorphism e.inv.ringMap.isDPMorphism n ω

abbrev evaluation : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  (CategoryTheory.evaluation _ _).obj (op U)

local notation "ev" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Poincare.evaluation U
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormComplex.complex H Q π
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Augmentation.ambientPresheaf Q
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.Poincare.complex R σ (OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.ideal (Q.obj U)) (OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.dividedPowers (Q.obj U))

def evaluationComponentIso (n : ℕ) :
    (((ev).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X n ≅ (P).X n :=
  (formsEquiv H Q π σ U e he n).toAddCommGrpIso

theorem evaluation_d (n : ℕ) :
    (((ev).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).d n (n + 1) ≫
        (evaluationComponentIso H Q π σ U e he (n + 1)).hom =
      (evaluationComponentIso H Q π σ U e he n).hom ≫ (P).d n (n + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro ω
  change formsEquiv H Q π σ U e he (n + 1) (((K).d n (n + 1)).app (op U) ω) =
    (P).d n (n + 1) (formsEquiv H Q π σ U e he n ω)
  rw [FormComplex.complex_d]
  exact (formsEquiv_differential H Q π σ U e he n ω).trans
    (Additive.Poincare.complex_d_apply R σ (Q.obj U).ideal (Q.obj U).dividedPowers n
      (formsEquiv H Q π σ U e he n ω)).symm

def evaluationIso : ((ev).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅ P :=
  HomologicalComplex.Hom.isoOfComponents (evaluationComponentIso H Q π σ U e he) (by
    intro n m h
    change n + 1 = m at h
    subst m
    exact (evaluation_d H Q π σ U e he n).symm)

def sourceIso :
    ((ev).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ _).obj A) ≅
      (CochainComplex.single₀ AddCommGrpCat.{u}).obj (AddCommGrpCat.of R) :=
  (HomologicalComplex.singleMapHomologicalComplex ev (ComplexShape.up ℕ) 0).app A

omit [Fact p.Prime] in
theorem sourceIso_inv_zero : (sourceIso Q U).inv.f 0 = 𝟙 (AddCommGrpCat.of R) := by
  exact (HomologicalComplex.singleMapHomologicalComplex_inv_app_self ev (ComplexShape.up ℕ) 0 A).trans
    (by
      simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
      rfl)

abbrev evaluatedAugmentation := ((ev).mapHomologicalComplex (ComplexShape.up ℕ)).map
  (Augmentation.augmentation H Q π)

def transportedAugmentation : (CochainComplex.single₀ AddCommGrpCat.{u}).obj (AddCommGrpCat.of R) ⟶ P :=
  (sourceIso Q U).inv ≫ evaluatedAugmentation H Q π U ≫ (evaluationIso H Q π σ U e he).hom

theorem transportedAugmentation_zero (a : R) :
    (transportedAugmentation H Q π σ U e he).f 0 a =
      formsEquiv H Q π σ U e he 0 (Augmentation.constants H Q π U a) := by
  change (evaluationIso H Q π σ U e he).hom.f 0
    ((evaluatedAugmentation H Q π U).f 0 ((sourceIso Q U).inv.f 0 a)) = _
  rw [sourceIso_inv_zero]
  change formsEquiv H Q π σ U e he 0 (((Augmentation.augmentation H Q π).f 0).app (op U) a) = _
  rw [Augmentation.augmentation_zero]
  rfl

variable [Fintype σ]

theorem augmentation_comparison : transportedAugmentation H Q π σ U e he =
    Additive.Poincare.augmentation R σ (Q.obj U).ideal (Q.obj U).dividedPowers := by
  apply HomologicalComplex.from_single_hom_ext
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change R at a
  refine (transportedAugmentation_zero H Q π σ U e he a).trans ?_
  rw [Augmentation.constants_symbol, formsEquiv_symbol]
  have h : e.hom.ringMap ((π.app U).ringMap a) = algebraMap R (G).ring a :=
    congrArg (fun α : G ⟶ Q.obj U => α.ringMap a) he
  have hs : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R (G).ring (G).ideal (G).dividedPowers
      (e.hom.ringMap ((π.app U).ringMap a)) (fun i : Fin 0 => e.hom.ringMap i.elim0) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R (G).ring (G).ideal (G).dividedPowers
        (algebraMap R (G).ring a) (fun i : Fin 0 => i.elim0) := by
    rw [h]
    congr 1
    funext i
    exact i.elim0
  exact hs.trans (Additive.Poincare.augmentation_zero R σ (Q.obj U).ideal (Q.obj U).dividedPowers a).symm

include e he in
theorem evaluatedAugmentation_quasiIso : QuasiIso (evaluatedAugmentation H Q π U) := by
  have h : QuasiIso (transportedAugmentation H Q π σ U e he) := by
    rw [augmentation_comparison]
    infer_instance
  exact (quasiIso_iff_comp_right _ (evaluationIso H Q π σ U e he).hom).mp
    ((quasiIso_iff_comp_left (sourceIso Q U).inv _).mp h)

theorem augmentation_quasiIso
    (h : ∀ U, ∃ e : Crystalline.DividedCoordinates.object (Q.obj U) σ ≅ H.obj U,
      e.hom ≫ π.app U = Crystalline.DividedCoordinates.projection (Q.obj U) σ) :
    QuasiIso (Augmentation.augmentation H Q π) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
  intro U
  obtain ⟨e, he⟩ := h U.unop
  exact evaluatedAugmentation_quasiIso H Q π σ U.unop e he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Poincare
