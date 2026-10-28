import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Parameters
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SurjectiveLocus
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Specialization

noncomputable section

/-! Arithmetic specialization in any nonempty locally finite-type parameter
scheme. A closed point supplies the finite residue extension, and algebraic
closedness extends the specified complex embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
  (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom] [Nonempty X.left]

/-- Construct an arithmetic parameter point, preserving the specified
number field and extending its chosen complex embedding. -/
theorem arithmetic_parameter_exists (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ) (_p : Over.mk B.fieldExtension ⟶ X),
      B.denominator = N := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (X := X.left) (Z := Set.univ) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hclosed : IsClosed {x} := hx
  let qK := Spec.map (CommRingCat.ofHom (algebraMap ℚ K))
  have : IsFinite qK := by
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : LocallyOfFiniteType (X.hom ≫ qK) := inferInstance
  let L := X.left.residueField x
  have : NumberField L := ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints.Abelian.residueField_numberField_of_closed (X.hom ≫ qK) x hclosed
  let pL := X.left.fromSpecResidueField x
  let j : K →+* L := (Spec.preimage (pL ≫ X.hom)).hom
  have hj : Spec.map (CommRingCat.ofHom j) = pL ≫ X.hom := Spec.map_preimage _
  let : Algebra K L := j.toAlgebra
  have : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let : Algebra K ℂ := κ.toAlgebra
  let e : L →ₐ[K] ℂ := IsAlgClosed.lift
  let B : Base.ArithmeticBaseExtension K κ := {
    extension := ⟨L⟩
    embedding := e.toRingHom
    embedding_extends := by
      ext a
      exact e.commutes a
    denominator := N
    denominator_ne_zero := hN }
  exact ⟨B, Over.homMk pL hj.symm, rfl⟩

omit [Nonempty X.left] in
/-- A complex surjective fiber of a proper family map produces an
arithmetic surjective fiber in the same constructed closed locus. -/
theorem arithmetic_surjective_specialization
    {V W : Over X.left} (f : V ⟶ W) [IsProper f.left] [UniversallyOpen W.hom]
    (c : Spec (.of ℂ) ⟶ X.left) (hc : Surjective ((Over.pullback c).map f).left)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ) (p : Over.mk B.fieldExtension ⟶ X),
      B.denominator = N ∧ Surjective ((Over.pullback p.left).map f).left := by
  let Z := Over.mk ((SurjectiveLocus.surjectiveParameterScheme f).hom ≫ X.hom)
  let j : Z ⟶ X := Over.homMk (SurjectiveLocus.surjectiveParameterScheme f).hom rfl
  have : LocallyOfFiniteType Z.hom := inferInstanceAs
    (LocallyOfFiniteType ((SurjectiveLocus.surjectiveParameterScheme f).hom ≫ X.hom))
  obtain ⟨cZ, _, _⟩ := (SurjectiveLocus.surjective_parameterScheme_classifies f c).mp hc
  have : Nonempty Z.left := ⟨cZ (IsLocalRing.closedPoint ℂ)⟩
  obtain ⟨B, pZ, hB⟩ := arithmetic_parameter_exists κ Z N hN
  refine ⟨B, pZ ≫ j, hB, ?_⟩
  apply (SurjectiveLocus.surjective_base_change_iff_range f _).mpr
  intro x hx
  rw [← SurjectiveLocus.surjectiveParameterScheme_range f]
  obtain ⟨t, rfl⟩ := hx
  exact ⟨pZ.left t, rfl⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Specialization
