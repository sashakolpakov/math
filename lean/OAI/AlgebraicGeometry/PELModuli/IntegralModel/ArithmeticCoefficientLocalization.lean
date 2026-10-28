import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base
import OAI.ArithmeticGeometry.Models.SpreadingOut.GroupDiagram

/-! # Arithmetic Coefficient Localization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-!
Existence of simultaneous smooth proper models over the exact arithmetic
bases used in IntegralModel. The schemes, arrows, group laws, generic isomorphisms,
and their compatibility are constructed from the proved Foundations/SpreadingOut coefficient
models. Any prescribed nonzero level is inverted in the resulting base.

The input diagram is over a number field. This result does not claim that
an arbitrary complex diagram has descended to a number field.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.NumberField

open OAI.ArithmeticGeometry.Models.SpreadingOut.GroupDiagram.Construction

section

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

/-- Enlarge the set of inverted rational primes while retaining the field
and its specified complex embedding. -/
abbrev Base.ArithmeticBaseExtension.withDenominator (B : Base.ArithmeticBaseExtension K κ) (D : ℕ) (hD : D ≠ 0) :
    Base.ArithmeticBaseExtension K κ :=
  { B with denominator := D, denominator_ne_zero := hD }

theorem Base.ArithmeticBaseExtension.divisor_isUnit (B : Base.ArithmeticBaseExtension K κ) (N : ℕ)
    (h : N ∣ B.denominator) : IsUnit (N : B.R) := by
  obtain ⟨d, hd⟩ := h
  have heq : (B.denominator : B.R) = (N : B.R) * (d : B.R) :=
    (congrArg (fun n : ℕ ↦ (n : B.R)) hd).trans (Nat.cast_mul N d)
  have hu := B.denominator_isUnit
  rw [heq] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- A finite coefficient base is dominated by an actual localization of
the ring of integers, compatibly with its generic point. -/
theorem Base.ArithmeticBaseExtension.coefficient_base_localization (B : Base.ArithmeticBaseExtension K κ)
    (s : Finset B.extension.carrier) (N : ℕ) (hN : N ≠ 0) :
    ∃ (D : ℕ) (hD : D ≠ 0), N ∣ D ∧
      let B' := B.withDenominator D hD
      ∃ b : B'.base ⟶ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 B.extension.carrier) B.extension.carrier s,
        B'.generic ≫ b = ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 B.extension.carrier) B.extension.carrier s := by
  obtain ⟨D, hD, hdiv, φ, hφ⟩ :=
    ArithmeticGeometry.Models.IntegerBase.Constructions.Foundations.finite_coefficient_ring_factors_through_integers B.extension.carrier s N hN
  refine ⟨D, hD, hdiv, Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩
  change Spec.map (CommRingCat.ofHom (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField B.extension.carrier D hD)) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hφ

end

/-- A simultaneous model of an actual finite number-field diagram, with
its commutative group structures and chosen generic comparisons, exists
over a localized ring of integers. No model-existence hypothesis is used. -/
theorem ArithmeticCoefficientLocalization.finite_smooth_proper_group_diagram_localized_model
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) (N : ℕ) (hN : N ≠ 0)
    {I α β : Type} [Finite I] [Finite α] [Finite β]
    (X : I → Over (Arithmetic.Open.fieldBase B.extension.carrier))
    (hs : ∀ i, Smooth (X i).hom) (hp : ∀ i, IsProper (X i).hom)
    (src dst : α → I) (f : ∀ a, X (src a) ⟶ X (dst a))
    (index : β → I) (group : ∀ b, GrpObj (X (index b)))
    (hcomm : ∀ b, letI := group b; IsCommMonObj (X (index b))) :
    ∃ (D : ℕ) (hD : D ≠ 0), N ∣ D ∧
      let B' := B.withDenominator D hD
      ∃ (M : I → Over B'.base) (fM : ∀ a, M (src a) ⟶ M (dst a))
        (e : ∀ i, (Over.pullback B'.generic).obj (M i) ≅ X i)
        (groupM : ∀ b, GrpObj (M (index b))),
        IsUnit (N : B'.R) ∧
        (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom) ∧
        (∀ a, (Over.pullback B'.generic).map (fM a) ≫ (e (dst a)).hom =
          (e (src a)).hom ≫ f a) ∧
        (∀ b,
          letI := group b
          letI := groupM b
          letI : GrpObj ((Over.pullback B'.generic).obj (M (index b))) :=
            Functor.grpObjObj
          IsCommMonObj (M (index b)) ∧ IsMonHom (e (index b)).hom) := by
  obtain ⟨s, M, fM, e, groupM, hM, he, hgroup⟩ :=
    ArithmeticGeometry.Models.SpreadingOut.GroupDiagram.Construction.finite_smooth_proper_group_diagram_coefficient_model X hs hp src dst f index group hcomm
  obtain ⟨D, hD, hdiv, b, hb⟩ := B.coefficient_base_localization s N hN
  let B' := B.withDenominator D hD
  let F := Over.pullback b
  let G := Over.pullback B'.generic
  let H := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 B.extension.carrier) B.extension.carrier s)
  let c : F ⋙ G ≅ H :=
    (Over.pullbackComp B'.generic b).symm ≪≫
      eqToIso (congrArg (fun k ↦ Over.pullback k) hb)
  let ec (i : I) : G.obj (F.obj (M i)) ≅ H.obj (M i) := c.app (M i)
  let groupN (j : β) : GrpObj (F.obj (M (index j))) := by
    let := groupM j
    exact Functor.grpObjObj (F := F)
  refine ⟨D, hD, hdiv, (fun i ↦ F.obj (M i)), (fun a ↦ F.map (fM a)),
    (fun i ↦ ec i ≪≫ e i), groupN, B'.divisor_isUnit N hdiv, ?_, ?_, ?_⟩
  · intro i
    have := (hM i).1
    have := (hM i).2
    exact ⟨inferInstanceAs (Smooth (pullback.snd (M i).hom b)),
      inferInstanceAs (IsProper (pullback.snd (M i).hom b))⟩
  · intro a
    have hc : G.map (F.map (fM a)) ≫ (ec (dst a)).hom =
        (ec (src a)).hom ≫ H.map (fM a) := c.hom.naturality (fM a)
    change G.map (F.map (fM a)) ≫ (ec (dst a)).hom ≫ (e (dst a)).hom =
      ((ec (src a)).hom ≫ (e (src a)).hom) ≫ f a
    rw [← Category.assoc, hc, Category.assoc, he, Category.assoc]
  · intro j
    let := group j
    let := groupM j
    let : GrpObj (F.obj (M (index j))) := groupN j
    let : GrpObj (G.obj (F.obj (M (index j)))) := Functor.grpObjObj (F := G)
    let : GrpObj (H.obj (M (index j))) := Functor.grpObjObj (F := H)
    have : IsCommMonObj (M (index j)) := (hgroup j).1
    refine ⟨inferInstanceAs (IsCommMonObj (F.obj (M (index j)))), ?_⟩
    have : IsMonHom (ec (index j)).hom :=
      ArithmeticGeometry.Models.SpreadingOut.GroupBaseChange.Construction.baseChange_comparison_group_hom F G H c (M (index j))
    have : IsMonHom (e (index j)).hom := (hgroup j).2
    exact inferInstanceAs (IsMonHom ((ec (index j)).hom ≫ (e (index j)).hom))

end

/-! A nonzero coefficient of an existing arithmetic base can be
inverted by enlarging its natural denominator, retaining the same
number field and the exact generic map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.NumberField

theorem Base.ArithmeticBaseExtension.coefficient_isUnit_after_localization
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) (r : B.R) (hr : r ≠ 0)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (D : ℕ) (hD : D ≠ 0), N ∣ D ∧ B.denominator ∣ D ∧
      let B' := B.withDenominator D hD
      ∃ φ : B.R →+* B'.R, B'.toField.comp φ = B.toField ∧ IsUnit (φ r) := by
  obtain ⟨D, hD, hdiv, hcoeff⟩ := ArithmeticGeometry.Models.Algebra.Constructions.Foundations.finite_coefficients_in_localized_integers
    B.extension.carrier (fun _ : Unit => (B.toField r)⁻¹)
    (N * B.denominator) (mul_ne_zero hN B.denominator_ne_zero)
  let B' := B.withDenominator D hD
  have hBD : B.denominator ∣ D := (dvd_mul_left B.denominator N).trans hdiv
  have hND : N ∣ D := (dvd_mul_right N B.denominator).trans hdiv
  have hb : IsUnit (algebraMap (𝓞 B.extension.carrier) B'.R
      (B.denominator : 𝓞 B.extension.carrier)) := by
    simpa only [map_natCast] using B'.divisor_isUnit B.denominator hBD
  let φ : B.R →+* B'.R := IsLocalization.Away.lift (B.denominator : 𝓞 B.extension.carrier) hb
  have hφ : B'.toField.comp φ = B.toField := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (B.denominator : 𝓞 B.extension.carrier))
    ext a
    change B'.toField (φ (algebraMap (𝓞 B.extension.carrier) B.R a)) =
      B.toField (algebraMap (𝓞 B.extension.carrier) B.R a)
    rw [IsLocalization.Away.lift_eq]
    exact (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap B.extension.carrier D hD a).trans
      (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap B.extension.carrier B.denominator B.denominator_ne_zero a).symm
  obtain ⟨v, hv⟩ := hcoeff ()
  have hr' : B.toField r ≠ 0 := fun h => hr (B.toField_injective (h.trans (map_zero _).symm))
  have hunit : IsUnit (φ r) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨v, ?_⟩
    apply B'.toField_injective
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (RingHom.congr_fun hφ r) hv).trans (mul_inv_cancel₀ hr')
  exact ⟨D, hD, hND, hBD, φ, hφ, hunit⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
