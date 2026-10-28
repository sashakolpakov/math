import OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD

/-! # Quotient Multivariable Mk -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableMk.QuotientMultivariablePrimitive

noncomputable section

/-!
# Coordinate primitives and constants on finite PD quotients

All coordinate primitives descend by base linearity. Their right-inverse
and commutation identities survive reduction, and composing their
coordinate projections retains exactly the quotient constant coefficient.
-/

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a)) (L : Ideal R)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "Q" => L.map (algebraMap R G)
local notation "B" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.Ring R σ L
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.quotient R σ L
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.derivation R σ K h I δ hunit L
local notation "dG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation.derivation R σ K h I δ hunit
local notation "SG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Primitive.MultivariablePrimitive.primitive R σ K h

def constants : (R ⧸ L) →ₐ[R] B :=
  Ideal.Quotient.liftₐ L (Algebra.ofId R B) (fun _a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))

theorem constants_mk (a : R) : constants R σ L (Ideal.Quotient.mk L a) = q (algebraMap R G a) := rfl

def primitive (i : σ) : B →ₗ[R] B := Base.IdealQuotient.BaseIdealQuotient.map L (SG i)

theorem primitive_quotient (i : σ) (a : G) : primitive R σ K h L i (q a) = q (SG i a) := rfl

def constantCoefficient : B →ₗ[R] (R ⧸ L) :=
  ((Q).restrictScalars R).liftQ
    (L.mkQ.comp (Multivariable.Constants.MultivariableConstants.constantCoefficient R σ K h)) (by
      intro a ha
      apply Submodule.Quotient.mk_eq_zero _ |>.mpr
      have hm := Base.IdealQuotient.BaseIdealQuotient.map_mem L (Multivariable.Constants.MultivariableConstants.constantCoefficient R σ K h) ha
      simpa only [Algebra.algebraMap_self, Ideal.map_id] using hm)

theorem constantCoefficient_quotient (a : G) : constantCoefficient R σ K h L (q a) =
    Ideal.Quotient.mk L (Multivariable.Constants.MultivariableConstants.constantCoefficient R σ K h a) := rfl

theorem derivation_primitive (i : σ) (a : B) : d i (primitive R σ K h L i a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change d i (primitive R σ K h L i (q a)) = q a
  rw [primitive_quotient, QuotientMultivariableD.QuotientMultivariableForms.derivation_quotient,
    Multivariable.Primitive.MultivariablePrimitive.derivation_primitive]

theorem derivation_primitive_commute (i j : σ) (hji : j ≠ i) (a : B) :
    d j (primitive R σ K h L i a) = primitive R σ K h L i (d j a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change d j (primitive R σ K h L i (q a)) = primitive R σ K h L i (d j (q a))
  rw [primitive_quotient, QuotientMultivariableD.QuotientMultivariableForms.derivation_quotient,
    QuotientMultivariableD.QuotientMultivariableForms.derivation_quotient, primitive_quotient]
  exact congrArg q (LinearMap.congr_fun
    (Multivariable.Primitive.MultivariablePrimitive.derivation_primitive_commute R σ K h I δ hunit i j (Ne.symm hji)) a)

theorem constantCoefficient_constants :
    (constantCoefficient R σ K h L).comp (constants R σ L).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change constantCoefficient R σ K h L (constants R σ L (Ideal.Quotient.mk L a)) = Ideal.Quotient.mk L a
  rw [constants_mk, constantCoefficient_quotient]
  exact congrArg (Ideal.Quotient.mk L)
    (LinearMap.congr_fun (Multivariable.Constants.MultivariableConstants.constantCoefficient_constants R σ K h) a)

theorem derivation_constants (i : σ) (a : R ⧸ L) : d i (constants R σ L a) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [constants_mk, QuotientMultivariableD.QuotientMultivariableForms.derivation_quotient, Derivation.map_algebraMap, map_zero]

def derivatives (i : σ) : Module.End R B := (d i).toLinearMap

local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableMk.QuotientMultivariablePrimitive.derivatives R σ K h I δ hunit L
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive R σ K h L

theorem coordinateProjection_quotient (i : σ) (a : G) :
    Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ B D i (S i) (q a) =
      q (Multivariable.Primitive.MultivariablePrimitive.projection R σ K h i a) := by
  change q a - primitive R σ K h L i (d i (q a)) = _
  rw [QuotientMultivariableD.QuotientMultivariableForms.derivation_quotient, primitive_quotient, ← map_sub]
  exact congrArg q (sub_eq_iff_eq_add.mpr
    ((Multivariable.Primitive.MultivariablePrimitive.primitive_derivation R σ K h I δ hunit i a).symm.trans (add_comm _ _)))

theorem coefficientProjection_quotient (l : List σ) (a : G) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ B D S l (q a) =
      q (Multivariable.Constants.MultivariableConstants.successive R σ K h l a) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    change Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ B D S l
      (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ B D i (S i) (q a)) = _
    rw [coordinateProjection_quotient]
    exact ih (Multivariable.Primitive.MultivariablePrimitive.projection R σ K h i a)

theorem coefficientProjection_constants (l : List σ) (hl : ∀ i, i ∈ l) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ B D S l =
      (constants R σ L).toLinearMap.comp (constantCoefficient R σ K h L) := by
  apply LinearMap.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ B D S l (q a) =
    constants R σ L (constantCoefficient R σ K h L (q a))
  rw [coefficientProjection_quotient, constantCoefficient_quotient, constants_mk,
    Multivariable.Constants.MultivariableConstants.successive_eq_constants R σ K h l hl]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableMk.QuotientMultivariablePrimitive
