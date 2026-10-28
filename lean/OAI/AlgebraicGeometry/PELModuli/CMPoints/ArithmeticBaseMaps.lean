import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ArithmeticCoefficientLocalization

/-! # Arithmetic Base Maps -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticBaseMaps

noncomputable section

section

/-! Enlarge an existing arithmetic localization while retaining its
field, embedding, and actual map from the original arithmetic base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D)

def arithmeticEnlargementRingHom : B.R →+* (B.withDenominator D hD).R :=
  IsLocalization.Away.lift (B.denominator : NumberField.RingOfIntegers B.extension.carrier)
    (g := algebraMap (NumberField.RingOfIntegers B.extension.carrier) (B.withDenominator D hD).R)
    (by simpa only [map_natCast] using (B.withDenominator D hD).divisor_isUnit B.denominator hdiv)

theorem arithmeticEnlargementRingHom_integers (a : NumberField.RingOfIntegers B.extension.carrier) :
    arithmeticEnlargementRingHom B D hD hdiv
      (algebraMap (NumberField.RingOfIntegers B.extension.carrier) B.R a) =
        algebraMap (NumberField.RingOfIntegers B.extension.carrier) (B.withDenominator D hD).R a :=
  IsLocalization.Away.lift_eq _ _ a

theorem arithmeticEnlargementRingHom_field :
    (B.withDenominator D hD).toField.comp (arithmeticEnlargementRingHom B D hD hdiv) = B.toField := by
  apply IsLocalization.ringHom_ext (Submonoid.powers
    (B.denominator : NumberField.RingOfIntegers B.extension.carrier))
  ext a
  change (B.withDenominator D hD).toField
      (arithmeticEnlargementRingHom B D hD hdiv
        (algebraMap (NumberField.RingOfIntegers B.extension.carrier) B.R a)) =
    B.toField (algebraMap (NumberField.RingOfIntegers B.extension.carrier) B.R a)
  rw [arithmeticEnlargementRingHom_integers]
  exact (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap _ _ _ a).trans
    (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap _ _ _ a).symm

def arithmeticEnlargement : (B.withDenominator D hD).base ⟶ B.base :=
  Spec.map (CommRingCat.ofHom (arithmeticEnlargementRingHom B D hD hdiv))

theorem arithmeticEnlargement_generic :
    (B.withDenominator D hD).generic ≫ arithmeticEnlargement B D hD hdiv = B.generic := by
  change Spec.map (CommRingCat.ofHom (B.withDenominator D hD).toField) ≫
    Spec.map (CommRingCat.ofHom (arithmeticEnlargementRingHom B D hD hdiv)) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (arithmeticEnlargementRingHom_field B D hD hdiv)

theorem arithmeticEnlargement_complex :
    (B.withDenominator D hD).complexPoint ≫ arithmeticEnlargement B D hD hdiv = B.complexPoint := by
  change (Spec.map (CommRingCat.ofHom B.embedding) ≫ (B.withDenominator D hD).generic) ≫ _ = _
  rw [Category.assoc, arithmeticEnlargement_generic]
  rfl

end

/-! Actual maps of arithmetic bases induced by specified field maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  {κ : K →+* ℂ} {κL : L →+* ℂ}
  (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (C : IntegralModel.Base.ArithmeticBaseExtension L κL)
  (i : B.extension.carrier →+* C.extension.carrier) (hdiv : B.denominator ∣ C.denominator)

def arithmeticBaseRingHom : B.R →+* C.R :=
  IsLocalization.Away.lift (B.denominator : NumberField.RingOfIntegers B.extension.carrier)
    (g := (algebraMap (NumberField.RingOfIntegers C.extension.carrier) C.R).comp
      (NumberField.RingOfIntegers.mapRingHom i))
    (by simpa only [RingHom.comp_apply, map_natCast] using C.divisor_isUnit B.denominator hdiv)

theorem arithmeticBaseRingHom_integers (a : NumberField.RingOfIntegers B.extension.carrier) :
    arithmeticBaseRingHom B C i hdiv
      (algebraMap (NumberField.RingOfIntegers B.extension.carrier) B.R a) =
        algebraMap (NumberField.RingOfIntegers C.extension.carrier) C.R
          (NumberField.RingOfIntegers.mapRingHom i a) :=
  IsLocalization.Away.lift_eq _ _ a

theorem arithmeticBaseRingHom_field :
    C.toField.comp (arithmeticBaseRingHom B C i hdiv) = i.comp B.toField := by
  apply IsLocalization.ringHom_ext (Submonoid.powers
    (B.denominator : NumberField.RingOfIntegers B.extension.carrier))
  apply RingHom.ext
  intro a
  change C.toField (arithmeticBaseRingHom B C i hdiv (algebraMap _ B.R a)) =
    i (B.toField (algebraMap _ B.R a))
  rw [arithmeticBaseRingHom_integers]
  exact (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap _ _ _ _).trans
    (congrArg i (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap _ _ _ a)).symm

def arithmeticBaseMap : C.base ⟶ B.base :=
  Spec.map (CommRingCat.ofHom (arithmeticBaseRingHom B C i hdiv))

theorem arithmeticBaseMap_generic :
    C.generic ≫ arithmeticBaseMap B C i hdiv = Spec.map (CommRingCat.ofHom i) ≫ B.generic := by
  change Spec.map (CommRingCat.ofHom C.toField) ≫
    Spec.map (CommRingCat.ofHom (arithmeticBaseRingHom B C i hdiv)) =
    Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom B.toField)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (arithmeticBaseRingHom_field B C i hdiv)

theorem arithmeticBaseMap_complex (hi : C.embedding.comp i = B.embedding) :
    C.complexPoint ≫ arithmeticBaseMap B C i hdiv = B.complexPoint := by
  change (Spec.map (CommRingCat.ofHom C.embedding) ≫ C.generic) ≫ _ = _
  rw [Category.assoc, arithmeticBaseMap_generic, ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ B.generic) hi

theorem arithmeticBaseRingHom_enlarge (D : ℕ) (hD : D ≠ 0) (hCD : C.denominator ∣ D) :
    (arithmeticEnlargementRingHom C D hD hCD).comp (arithmeticBaseRingHom B C i hdiv) =
      arithmeticBaseRingHom B (C.withDenominator D hD) i (hdiv.trans hCD) := by
  apply RingHom.ext
  intro a
  apply (C.withDenominator D hD).toField_injective
  exact (RingHom.congr_fun (arithmeticEnlargementRingHom_field C D hD hCD)
    (arithmeticBaseRingHom B C i hdiv a)).trans
    ((RingHom.congr_fun (arithmeticBaseRingHom_field B C i hdiv) a).trans
      (RingHom.congr_fun (arithmeticBaseRingHom_field B (C.withDenominator D hD) i
        (hdiv.trans hCD)) a).symm)

theorem arithmeticBaseMap_enlarge (D : ℕ) (hD : D ≠ 0) (hCD : C.denominator ∣ D) :
    arithmeticEnlargement C D hD hCD ≫ arithmeticBaseMap B C i hdiv =
      arithmeticBaseMap B (C.withDenominator D hD) i (hdiv.trans hCD) := by
  dsimp only [arithmeticEnlargement, arithmeticBaseMap]
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (arithmeticBaseRingHom_enlarge B C i hdiv D hD hCD)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticBaseMaps
