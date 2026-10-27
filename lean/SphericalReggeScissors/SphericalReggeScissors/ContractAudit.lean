/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import SphericalReggeScissors.Scissors

/-!
# Contract consistency and necessity audit

Two small executable models guard against opposite specification errors.

1. `finiteContract` inhabits every field of the complete proof contract
   with finite carriers.  Thus the interface is not accidentally
   contradictory.
2. `boolCountermodel` has an involution and equal volumes, but distinct
   proposed class values.  It proves only that those two bare properties do
   not force class equality; it is not a model of the full geometric E1.
-/

namespace SphericalReggeScissors

/-! ## A finite model of the complete contract -/

/-- A one-element finite additive group used for every coefficient space
in the consistency model. -/
abbrev ContractPoint := Fin 0 → ℚ

private def contractPointKernelEquiv :
    (0 : ContractPoint →ₗ[ℚ] ContractPoint).ker ≃ₗ[ℚ] ContractPoint where
  toFun := fun _ ↦ 0
  invFun := fun _ ↦ 0
  left_inv := by
    intro x
    exact Subsingleton.elim _ _
  right_inv := by
    intro x
    exact Subsingleton.elim _ _
  map_add' := by
    intro x y
    exact Subsingleton.elim _ _
  map_smul' := by
    intro c x
    exact Subsingleton.elim _ _

/-- Finite witness for the relative-motivic input package. -/
def finiteMotivicInputs :
    MotivicInputs ContractPoint ContractPoint ContractPoint where
  RelativeObject := ContractPoint
  coefficient := fun _ ↦ 0
  isAlternatingFaceObject := fun _ ↦ True
  hasExactThreeGradedPieces := fun _ ↦ True
  strictThreeWeightHeart := True
  strict_three_weight_heart_constructed := trivial
  coproduct := 0
  primitiveComparison := contractPointKernelEquiv
  h1_vanishes := fun h ↦ Subsingleton.elim h 0

/-- Finite witness for the relative-object/coproduct/descent bridge. -/
def finiteCoproductBridge :
    CoproductBridge ContractPoint ContractPoint ContractPoint ContractPoint
      finiteMotivicInputs.coproduct where
  relativeOriginal := 0
  relativeReggeMate := 0
  splitPullback := 0
  finite_etale_sign_trace_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  movingLeft := fun _ ↦ 0
  movingRight := fun _ ↦ 0
  fixedLeft₀ := 0
  fixedLeft₁ := 0
  fixedRight₀ := 0
  fixedRight₁ := 0
  split_formula_original := Subsingleton.elim _ _
  split_formula_reggeMate := Subsingleton.elim _ _

/-- Finite witness for all specialization and injectivity inputs. -/
def finiteSpecializationInputs :
    SpecializationInputs ContractPoint ContractPoint ContractPoint ContractPoint
      ContractPoint ContractPoint ContractPoint where
  specialize := 0
  endpoint := 0
  middleSpecialize := 0
  quadricCoproduct := 0
  goncharov := 0
  duality := 0
  spherical := 0
  goncharov_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  duality_involutive := fun _ ↦ Subsingleton.elim _ _
  spherical_injective := fun _ _ _ ↦ Subsingleton.elim _ _

/-- Finite witness for the suspension/area/cancellation inputs. -/
def finiteScissorsInputs :
    ScissorsInputs ContractPoint ContractPoint ContractPoint ContractPoint
      (Fin 1) (Fin 1) where
  suspension := 0
  reduction := 0
  rationalize := 0
  rationalization_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  exact_at_full := by
    intro z _
    exact ⟨0, Subsingleton.elim _ _⟩
  area := 0
  volume := 0
  suspension_volume := by simp
  area_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  scissorsClass := fun _ ↦ 0
  decomposes := fun _ _ ↦ True
  pieceIsometric := fun _ _ ↦ True
  cancellation := by
    intro x y h
    exact ⟨{
      leftPieces := []
      rightPieces := []
      left_decomposition := trivial
      right_decomposition := trivial
      pairwise_isometric := .nil
    }⟩

/-- Finite witness for the two named E1 geometric certificates. -/
def finiteGeometricReggeInputs : GeometricReggeInputs (Fin 1) where
  isNondegeneratePhysicalReggePair := fun _ _ ↦ True
  hasGeometricAngleAndLengthAction := fun _ _ ↦ True

/--
An inhabited model of the entire proof contract whose coefficient and
tetrahedron carriers are finite.
-/
def finiteContract :
    ProofContract ContractPoint ContractPoint ContractPoint ContractPoint
      ContractPoint ContractPoint ContractPoint ContractPoint ContractPoint
      ContractPoint ContractPoint ContractPoint ContractPoint ContractPoint
      (Fin 1) (Fin 1) where
  motivic := finiteMotivicInputs
  coproductBridge := finiteCoproductBridge
  relativeOriginalObject := by
    change ContractPoint
    exact 0
  relativeReggeMateObject := by
    change ContractPoint
    exact 0
  original_face_object_constructed := trivial
  reggeMate_face_object_constructed := trivial
  original_exact_three_graded_pieces := trivial
  reggeMate_exact_three_graded_pieces := trivial
  relative_original_coefficient := Subsingleton.elim _ _
  relative_reggeMate_coefficient := Subsingleton.elim _ _
  specialization := finiteSpecializationInputs
  scissors := finiteScissorsInputs
  presentationComparison := LinearEquiv.refl ℚ ContractPoint
  original := 0
  reggeMate := 0
  geometry := finiteGeometricReggeInputs
  physical_regge_pair_realized := trivial
  geometric_angle_length_action_certified := trivial
  universalDefect := 0
  quadricDualDefect := 0
  goncharovSphericalDefect := 0
  reducedRationalDefect := 0
  reducedDefect := 0
  universal_defect_is_difference := Subsingleton.elim _ _
  quadric_coproduct_specialization := Subsingleton.elim _ _
  fibre_endpoint_eq_cG := fun _ ↦ Subsingleton.elim _ _
  duality_comparison := Subsingleton.elim _ _
  presentation_defect_comparison := Subsingleton.elim _ _
  rationalization_comparison := Subsingleton.elim _ _
  reduced_comparison := Subsingleton.elim _ _
  regge_volume := by simp

/-- The contract type is genuinely inhabited, rather than merely used as
an implication premise. -/
theorem finiteContract_exists :
    Nonempty
      (ProofContract ContractPoint ContractPoint ContractPoint ContractPoint
        ContractPoint ContractPoint ContractPoint ContractPoint ContractPoint
        ContractPoint ContractPoint ContractPoint ContractPoint ContractPoint
        (Fin 1) (Fin 1)) :=
  ⟨finiteContract⟩

/-- All coefficient carriers in `finiteContract` have finitely many
elements. -/
theorem contractPointFinite : Finite ContractPoint := inferInstance

/-- The tetrahedron carrier in `finiteContract` has finitely many
elements. -/
theorem contractTetrahedronFinite : Finite (Fin 1) := inferInstance

/-! ## Involution and volume by themselves are insufficient -/

/-- A deliberately weak fragment of the geometric information: an
involution and preservation of volume, together with an otherwise
unconstrained proposed class.  It does not encode E1's angle/length action. -/
structure BareReggeGeometry (Tetrahedron Volume ScissorsClass : Type*) where
  regge : Tetrahedron → Tetrahedron
  volume : Tetrahedron → Volume
  scissorsClass : Tetrahedron → ScissorsClass
  regge_involutive : Function.Involutive regge
  volume_invariant : ∀ t, volume (regge t) = volume t

/-- A two-tetrahedron model: Regge swaps the two objects, volume is
constant, and their scissors classes remain distinct. -/
def boolCountermodel : BareReggeGeometry Bool Unit Bool where
  regge := fun b ↦ !b
  volume := fun _ ↦ ()
  scissorsClass := id
  regge_involutive := by
    intro b
    cases b <;> rfl
  volume_invariant := by
    intro b
    rfl

/-- Equal volume and an involution do not logically force equality of an
arbitrary proposed class function.  This is weaker than a countermodel to
the complete E1 package. -/
theorem equal_volume_does_not_force_scissors_class :
    ∃ (G : BareReggeGeometry Bool Unit Bool) (t : Bool),
      G.volume t = G.volume (G.regge t) ∧
      G.scissorsClass t ≠ G.scissorsClass (G.regge t) := by
  refine ⟨boolCountermodel, false, rfl, ?_⟩
  decide

end SphericalReggeScissors
