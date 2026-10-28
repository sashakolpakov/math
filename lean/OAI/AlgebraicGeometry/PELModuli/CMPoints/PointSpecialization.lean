import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionLie
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Point Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Properness extends actual q-adic points over Z_q. The arithmetic
base map is constructed from the specified integral embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem PointSpecialization.proper_qadic_point_extends
    {q : ℕ} [Fact q.Prime] {X Y : Scheme} (f : X ⟶ Y) [IsProper f]
    (b : Spec (.of (PadicInt q)) ⟶ Y) (x : Spec (.of (Padic q)) ⟶ X)
    (hcomm : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (PadicInt q) (Padic q))) ≫ b) :
    ∃ z : Spec (.of (PadicInt q)) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap (PadicInt q) (Padic q))) ≫ z = x ∧ z ≫ f = b := by
  have hf : IsProper f := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hf
  let sq : ValuativeCommSq f := {
    R := PadicInt q
    K := Padic q
    i₁ := x
    i₂ := b
    commSq := ⟨hcomm⟩ }
  obtain ⟨l⟩ := (CommSq.HasLift.iff sq.commSq).mp (hf.1.1.1.existence sq)
  exact ⟨l.l, l.fac_left, l.fac_right⟩

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)

include R in
theorem Models.RankThreePELModel.GoodIntegralReduction.denominatorPrimeToQ : Nat.Coprime q M.arithmetic.denominator := by
  apply (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
  have hu : IsUnit (M.arithmetic.denominator : ZMod q) := by
    simpa only [map_natCast] using M.arithmetic.denominator_isUnit.map R.residue
  exact fun h => hu.ne_zero ((ZMod.natCast_eq_zero_iff _ _).mpr h)

include R in
theorem Models.RankThreePELModel.GoodIntegralReduction.integral_denominator_isUnit : IsUnit (j.integralEmbedding
    (M.arithmetic.denominator : NumberField.RingOfIntegers M.arithmetic.extension.carrier)) := by
  rw [map_natCast, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact R.denominatorPrimeToQ

def Models.RankThreePELModel.GoodIntegralReduction.integralPadicBaseMap : M.arithmetic.R →+* PadicInt q :=
  IsLocalization.Away.lift
    (M.arithmetic.denominator : NumberField.RingOfIntegers M.arithmetic.extension.carrier)
    R.integral_denominator_isUnit

theorem Models.RankThreePELModel.GoodIntegralReduction.integralPadicBaseMap_comp :
    R.integralPadicBaseMap.comp
      (algebraMap (NumberField.RingOfIntegers M.arithmetic.extension.carrier) M.arithmetic.R) =
        j.integralEmbedding := IsLocalization.Away.lift_comp _ R.integral_denominator_isUnit

theorem Models.RankThreePELModel.GoodIntegralReduction.integralPadicBaseMap_residue :
    PadicInt.toZMod.comp R.integralPadicBaseMap = R.residue := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (M.arithmetic.denominator :
      NumberField.RingOfIntegers M.arithmetic.extension.carrier))
  rw [RingHom.comp_assoc, R.integralPadicBaseMap_comp, R.residue_compatibility]
  rfl

theorem Models.RankThreePELModel.GoodIntegralReduction.integralPadicBaseMap_generic :
    PadicInt.Coe.ringHom.comp R.integralPadicBaseMap =
      (j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime)).comp
        M.arithmetic.toField := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (M.arithmetic.denominator :
      NumberField.RingOfIntegers M.arithmetic.extension.carrier))
  ext a
  have ha := RingHom.congr_fun R.integralPadicBaseMap_comp a
  have hb : M.arithmetic.toField
      (algebraMap (NumberField.RingOfIntegers M.arithmetic.extension.carrier) M.arithmetic.R a) =
        (a : M.arithmetic.extension.carrier) :=
    ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap _ _ _ a
  change (R.integralPadicBaseMap (algebraMap _ _ a) : Padic q) =
    j.completion (NumberField.FinitePlace.embedding j.prime
      (M.arithmetic.toField (algebraMap _ _ a)))
  exact (congrArg (PadicInt.Coe.ringHom : PadicInt q →+* Padic q) ha).trans
    ((RingHom.congr_fun j.integral_compatibility a).trans
      (congrArg (j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime)) hb.symm))

def Models.RankThreePELModel.GoodIntegralReduction.integralBasePoint : Spec (.of (PadicInt q)) ⟶ M.arithmetic.base :=
  Spec.map (CommRingCat.ofHom R.integralPadicBaseMap)

theorem Models.RankThreePELModel.GoodIntegralReduction.integralBasePoint_residue :
    Spec.map (CommRingCat.ofHom (PadicInt.toZMod : PadicInt q →+* ZMod q)) ≫
      R.integralBasePoint = R.specialBase := by
  rw [Models.RankThreePELModel.GoodIntegralReduction.integralBasePoint, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (PadicInt.toZMod.comp R.integralPadicBaseMap)) = _
  rw [R.integralPadicBaseMap_residue]
  rfl

/-- A point defined over a compatible number-field extension gives the
required arithmetic square over the chosen q-adic base. -/
theorem Models.RankThreePELModel.GoodIntegralReduction.fieldPoint_arithmetic_square
    {F : Type} [Field F]
    (iF : M.arithmetic.extension.carrier →+* F) (fF : F →+* Padic q)
    (hf : fF.comp iF = j.completion.toRingHom.comp
      (NumberField.FinitePlace.embedding j.prime))
    (X : Over M.arithmetic.base) (x : Spec (.of F) ⟶ X.left)
    (hx : x ≫ X.hom = Spec.map (CommRingCat.ofHom (iF.comp M.arithmetic.toField))) :
    (Spec.map (CommRingCat.ofHom fF) ≫ x) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (PadicInt q) (Padic q))) ≫
        R.integralBasePoint := by
  rw [Category.assoc, hx]
  dsimp only [Models.RankThreePELModel.GoodIntegralReduction.integralBasePoint]
  rw [← Spec.map_comp, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (fF.comp (iF.comp M.arithmetic.toField))) =
    Spec.map (CommRingCat.ofHom
      ((algebraMap (PadicInt q) (Padic q)).comp R.integralPadicBaseMap))
  rw [← RingHom.comp_assoc, hf, ← R.integralPadicBaseMap_generic]
  rfl

/-- Properness specializes a point defined over any compatible extension
field, on any of the given proper integral components. -/
theorem Models.RankThreePELModel.GoodIntegralReduction.fieldPoint_extends
    {F : Type} [Field F]
    (iF : M.arithmetic.extension.carrier →+* F) (fF : F →+* Padic q)
    (hf : fF.comp iF = j.completion.toRingHom.comp
      (NumberField.FinitePlace.embedding j.prime))
    (X : Over M.arithmetic.base) [IsProper X.hom] (x : Spec (.of F) ⟶ X.left)
    (hx : x ≫ X.hom = Spec.map (CommRingCat.ofHom (iF.comp M.arithmetic.toField))) :
    ∃ z : Spec (.of (PadicInt q)) ⟶ X.left,
      Spec.map (CommRingCat.ofHom (algebraMap (PadicInt q) (Padic q))) ≫ z =
        Spec.map (CommRingCat.ofHom fF) ≫ x ∧ z ≫ X.hom = R.integralBasePoint :=
  PointSpecialization.proper_qadic_point_extends X.hom R.integralBasePoint _
    (R.fieldPoint_arithmetic_square iF fF hf X x hx)

/-- An actual q-adic point on the prescribed proper integral component
extends to Z_q and hence supplies a point on its specified special fiber. -/
theorem Models.RankThreePELModel.GoodIntegralReduction.integral_family_point_extends (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (x : Spec (.of (Padic q)) ⟶ (M.integral a).toOver.left)
    (hx : x ≫ (M.integral a).toOver.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (PadicInt q) (Padic q))) ≫ R.integralBasePoint) :
    ∃ z : Spec (.of (PadicInt q)) ⟶ (M.integral a).toOver.left,
      Spec.map (CommRingCat.ofHom (algebraMap (PadicInt q) (Padic q))) ≫ z = x ∧
      z ≫ (M.integral a).toOver.hom = R.integralBasePoint := by
  obtain ⟨_, _, _, _, _, _, _, hp, _⟩ := hM.2.2 a
  let : IsProper (M.integral a).toOver.hom := hp
  exact PointSpecialization.proper_qadic_point_extends (M.integral a).toOver.hom R.integralBasePoint x hx

/-- The reduction is a morphism to the actual pullback special fiber. -/
def Models.RankThreePELModel.GoodIntegralReduction.specialPointOfIntegral (a : M.Family)
    (z : Spec (.of (PadicInt q)) ⟶ (M.integral a).toOver.left)
    (hz : z ≫ (M.integral a).toOver.hom = R.integralBasePoint) :
    Spec (.of (ZMod q)) ⟶ (R.specialFiber a).left :=
  CategoryTheory.Limits.pullback.lift
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : PadicInt q →+* ZMod q)) ≫ z)
    (𝟙 _) (by
      rw [Category.assoc, hz, R.integralBasePoint_residue, Category.id_comp])

/-- Base extension of that reduction to the specified algebraic closure. -/
def Models.RankThreePELModel.GoodIntegralReduction.geometricPointOfIntegral (a : M.Family)
    (z : Spec (.of (PadicInt q)) ⟶ (M.integral a).toOver.left)
    (hz : z ≫ (M.integral a).toOver.hom = R.integralBasePoint) :
    Spec (.of (AlgebraicClosure (ZMod q))) ⟶ R.geom a :=
  CategoryTheory.Limits.pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) ≫
      Spec.map (CommRingCat.ofHom (PadicInt.toZMod : PadicInt q →+* ZMod q)) ≫ z)
    (𝟙 _) (by
      rw [Category.assoc, Category.assoc, hz, R.integralBasePoint_residue,
        Category.id_comp, R.geometricBase_factors])

theorem Models.RankThreePELModel.GoodIntegralReduction.geometricPointOfIntegral_projection (a : M.Family)
    (z : Spec (.of (PadicInt q)) ⟶ (M.integral a).toOver.left)
    (hz : z ≫ (M.integral a).toOver.hom = R.integralBasePoint) :
    R.geometricPointOfIntegral a z hz ≫ R.projection a =
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) ≫
        Spec.map (CommRingCat.ofHom (PadicInt.toZMod : PadicInt q →+* ZMod q)) ≫ z :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
