import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertAdditivity
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorExact
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorCoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # K Theory -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.KTheory.Projective

noncomputable section

/-! The Grothendieck group of actual finite-type quasicoherent sheaves on
an arbitrary scheme, its invertible-sheaf tensor action, and the additive
Hilbert-polynomial index for an actual closed projective embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorExact

universe u

structure CoherentModule (A : Scheme.{u}) where
  sheaf : A.Modules
  quasicoherent : sheaf.IsQuasicoherent
  finiteType : sheaf.IsFiniteType

attribute [instance] CoherentModule.quasicoherent CoherentModule.finiteType

structure CoherentExactSequence (A : Scheme.{u}) where
  left : CoherentModule A
  middle : CoherentModule A
  right : CoherentModule A
  inclusion : left.sheaf ⟶ middle.sheaf
  projection : middle.sheaf ⟶ right.sheaf
  zero : inclusion ≫ projection = 0
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

def coherentExactRelation {A : Scheme.{u}} (S : CoherentExactSequence A) :
    FreeAbelianGroup (CoherentModule A) :=
  FreeAbelianGroup.of S.middle - FreeAbelianGroup.of S.left - FreeAbelianGroup.of S.right

def coherentK0Relations (A : Scheme.{u}) :
    AddSubgroup (FreeAbelianGroup (CoherentModule A)) :=
  AddSubgroup.closure (Set.range (coherentExactRelation (A := A)))

abbrev CoherentK0 (A : Scheme.{u}) :=
  FreeAbelianGroup (CoherentModule A) ⧸ coherentK0Relations A

def coherentK0Class {A : Scheme.{u}} (M : CoherentModule A) : CoherentK0 A :=
  QuotientAddGroup.mk' (coherentK0Relations A) (FreeAbelianGroup.of M)

theorem coherentK0Class_exact {A : Scheme.{u}} (S : CoherentExactSequence A) :
    coherentK0Class S.middle = coherentK0Class S.left + coherentK0Class S.right := by
  have hmem : coherentExactRelation S ∈ coherentK0Relations A :=
    AddSubgroup.subset_closure ⟨S, rfl⟩
  have hzero := (QuotientAddGroup.eq_zero_iff (coherentExactRelation S)).mpr hmem
  change (QuotientAddGroup.mk' (coherentK0Relations A)) (coherentExactRelation S) = 0 at hzero
  simp only [coherentExactRelation, map_sub] at hzero
  change coherentK0Class S.middle - coherentK0Class S.left - coherentK0Class S.right = 0 at hzero
  exact sub_eq_zero.mp (by simpa only [sub_sub] using hzero)

theorem coherentK0Class_eq_zero_of_isZero {A : Scheme.{u}}
    (M : CoherentModule A) (hM : IsZero M.sheaf) : coherentK0Class M = 0 := by
  have hz : (𝟙 M.sheaf) ≫ (𝟙 M.sheaf) = 0 := hM.eq_of_src _ _
  let S : CoherentExactSequence A :=
    { left := M
      middle := M
      right := M
      inclusion := 𝟙 M.sheaf
      projection := 𝟙 M.sheaf
      zero := hz
      shortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_of_isZero_X₂ _ hM) }
  have h := coherentK0Class_exact S
  change coherentK0Class M = coherentK0Class M + coherentK0Class M at h
  exact (add_left_cancel (a := coherentK0Class M) (by simpa only [add_zero] using h)).symm

theorem coherentK0Class_eq_of_iso {A : Scheme.{u}}
    (M N : CoherentModule A) (e : M.sheaf ≅ N.sheaf) : coherentK0Class M = coherentK0Class N := by
  let Z : CoherentModule A :=
    { sheaf := cokernel e.hom
      quasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel e.hom
      finiteType := AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel e.hom }
  let S : CoherentExactSequence A :=
    { left := M
      middle := N
      right := Z
      inclusion := e.hom
      projection := cokernel.π e.hom
      zero := cokernel.condition e.hom
      shortExact := ShortComplex.ShortExact.mk (ShortComplex.cokernelSequence_exact e.hom) }
  have hz : coherentK0Class Z = 0 := coherentK0Class_eq_zero_of_isZero Z (isZero_cokernel_of_epi e.hom)
  have h := coherentK0Class_exact S
  change coherentK0Class N = coherentK0Class M + coherentK0Class Z at h
  rw [hz, add_zero] at h
  exact h.symm

def coherentCokernel {A : Scheme.{u}} {M N : CoherentModule A}
    (a : M.sheaf ⟶ N.sheaf) : CoherentModule A where
  sheaf := cokernel a
  quasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel a
  finiteType := AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel a

theorem coherentCokernel_class {A : Scheme.{u}} {M N : CoherentModule A}
    (a : M.sheaf ⟶ N.sheaf) [Mono a] :
    coherentK0Class (coherentCokernel a) = coherentK0Class N - coherentK0Class M := by
  let S : CoherentExactSequence A :=
    { left := M
      middle := N
      right := coherentCokernel a
      inclusion := a
      projection := cokernel.π a
      zero := cokernel.condition a
      shortExact := by
        change (ShortComplex.mk a (cokernel.π a) (cokernel.condition a)).ShortExact
        exact { exact := ShortComplex.cokernelSequence_exact a } }
  have h := coherentK0Class_exact S
  change coherentK0Class N = coherentK0Class M + coherentK0Class (coherentCokernel a) at h
  rw [h, add_sub_cancel_left]

noncomputable local instance coherentTensorK0Monoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def coherentTensorModule {A : Scheme.{u}} (L : A.Modules)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) (M : CoherentModule A) : CoherentModule A where
  sheaf := (AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence.invertibleRightTensorEquivalence L hL).functor.obj M.sheaf
  quasicoherent := hL.tensorObj_isQuasicoherent
  finiteType := hL.tensorObj_isFiniteType

def coherentTensorSequence {A : Scheme.{u}} (L : A.Modules)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) (S : CoherentExactSequence A) :
    CoherentExactSequence A := by
  let F := (AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence.invertibleRightTensorEquivalence L hL).functor
  let T := (ShortComplex.mk S.inclusion S.projection S.zero).map F
  exact
    { left := coherentTensorModule L hL S.left
      middle := coherentTensorModule L hL S.middle
      right := coherentTensorModule L hL S.right
      inclusion := T.f
      projection := T.g
      zero := T.zero
      shortExact := S.shortExact.map_of_exact F }

def coherentTensorClassOnFree {A : Scheme.{u}} (L : A.Modules)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) :
    FreeAbelianGroup (CoherentModule A) →+ CoherentK0 A :=
  FreeAbelianGroup.lift (fun M => coherentK0Class (coherentTensorModule L hL M))

theorem coherentK0Relations_le_tensorKernel {A : Scheme.{u}}
    (L : A.Modules) (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) :
    coherentK0Relations A ≤ (coherentTensorClassOnFree L hL).ker := by
  apply (AddSubgroup.closure_le _).2
  rintro _ ⟨S, rfl⟩
  change coherentTensorClassOnFree L hL (coherentExactRelation S) = 0
  simp only [coherentTensorClassOnFree, coherentExactRelation, map_sub,
    FreeAbelianGroup.lift_apply_of]
  have h := coherentK0Class_exact (coherentTensorSequence L hL S)
  change coherentK0Class (coherentTensorModule L hL S.middle) =
    coherentK0Class (coherentTensorModule L hL S.left) +
      coherentK0Class (coherentTensorModule L hL S.right) at h
  rw [h]
  abel

def coherentTensorK0 {A : Scheme.{u}} (L : A.Modules)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) : CoherentK0 A →+ CoherentK0 A :=
  QuotientAddGroup.lift (coherentK0Relations A) (coherentTensorClassOnFree L hL)
    (coherentK0Relations_le_tensorKernel L hL)

@[simp]
theorem coherentTensorK0_class {A : Scheme.{u}} (L : A.Modules)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) (M : CoherentModule A) :
    coherentTensorK0 L hL (coherentK0Class M) =
      coherentK0Class (coherentTensorModule L hL M) := by
  change coherentTensorClassOnFree L hL (FreeAbelianGroup.of M) = _
  exact FreeAbelianGroup.lift_apply_of _ _

local instance coherentTensorK0LawsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem coherentK0_hom_ext {A : Scheme.{u}} {G : Type*} [AddCommGroup G]
    (f g : CoherentK0 A →+ G) (h : ∀ M : CoherentModule A, f (coherentK0Class M) = g (coherentK0Class M)) :
    f = g := by
  let p := QuotientAddGroup.mk' (coherentK0Relations A)
  have he : f.comp p = g.comp p := FreeAbelianGroup.lift_ext _ _ h
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (coherentK0Relations A) x
  exact DFunLike.congr_fun he y

theorem coherentTensorK0_congr {A : Scheme.{u}}
    {L N : A.Modules} (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L)
    (hN : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible N) (e : L ≅ N) :
    coherentTensorK0 L hL = coherentTensorK0 N hN := by
  apply coherentK0_hom_ext
  intro M
  rw [coherentTensorK0_class, coherentTensorK0_class]
  exact coherentK0Class_eq_of_iso _ _ (Iso.refl M.sheaf ⊗ᵢ e)

theorem coherentTensorK0_unit (A : Scheme.{u}) :
    coherentTensorK0 (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A) AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit =
      AddMonoidHom.id (CoherentK0 A) := by
  apply coherentK0_hom_ext
  intro M
  rw [coherentTensorK0_class]
  exact coherentK0Class_eq_of_iso _ M
    ((Iso.refl M.sheaf ⊗ᵢ (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso A).symm) ≪≫ ρ_ M.sheaf)

theorem coherentTensorK0_comp {A : Scheme.{u}}
    (L N : A.Modules) (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L)
    (hN : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible N) :
    (coherentTensorK0 L hL).comp (coherentTensorK0 N hN) =
      coherentTensorK0 (N ⊗ L) ((hN.tensorObj hL).of_iso (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso N L)) := by
  apply coherentK0_hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, coherentTensorK0_class]
  exact coherentK0Class_eq_of_iso _ _ (α_ M.sheaf N L)

theorem coherentTensorK0_commute {A : Scheme.{u}}
    (L N : A.Modules) (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L)
    (hN : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible N) :
    (coherentTensorK0 L hL).comp (coherentTensorK0 N hN) =
      (coherentTensorK0 N hN).comp (coherentTensorK0 L hL) := by
  let : SymmetricCategory A.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory A
  rw [coherentTensorK0_comp, coherentTensorK0_comp]
  exact coherentTensorK0_congr _ _ (β_ N L)

def coherentTensorEnd {A : Scheme.{u}} (L : A.Modules)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) : AddMonoid.End (CoherentK0 A) :=
  coherentTensorK0 L hL

def coherentTensorDifference {A : Scheme.{u}} (L : A.Modules)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) : AddMonoid.End (CoherentK0 A) :=
  coherentTensorEnd L hL - 1

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ} {A : Scheme.{u}}
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f] (j : Fin (r + 1))

def coherentHilbertOnFree : FreeAbelianGroup (CoherentModule A) →+ Polynomial ℚ :=
  FreeAbelianGroup.lift (fun M => AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M.sheaf j)

theorem coherentK0Relations_le_hilbertKernel :
    coherentK0Relations A ≤ (coherentHilbertOnFree f j).ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro _ ⟨S, rfl⟩
  change coherentHilbertOnFree f j (coherentExactRelation S) = 0
  simp only [coherentHilbertOnFree, coherentExactRelation, map_sub,
    FreeAbelianGroup.lift_apply_of]
  have he := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertAdditivity.Construction.closedProjectiveHilbertPolynomial_add_of_shortExact f
    (ShortComplex.mk S.inclusion S.projection S.zero) S.shortExact j
  change AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f S.middle.sheaf j =
    AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f S.left.sheaf j +
      AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f S.right.sheaf j at he
  rw [he]
  abel

def coherentHilbertIndex : CoherentK0 A →+ Polynomial ℚ :=
  QuotientAddGroup.lift (coherentK0Relations A) (coherentHilbertOnFree f j)
    (coherentK0Relations_le_hilbertKernel f j)

@[simp]
theorem coherentHilbertIndex_class (M : CoherentModule A) :
    coherentHilbertIndex f j (coherentK0Class M) =
      AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M.sheaf j := by
  change coherentHilbertOnFree f j (FreeAbelianGroup.of M) = _
  exact FreeAbelianGroup.lift_apply_of _ _

def coherentHilbertEulerIndex : CoherentK0 A →+ ℚ where
  toFun x := (coherentHilbertIndex f j x).eval 0
  map_zero' := by rw [map_zero, Polynomial.eval_zero]
  map_add' x y := by rw [map_add, Polynomial.eval_add]

@[simp]
theorem coherentHilbertEulerIndex_class (M : CoherentModule A) :
    coherentHilbertEulerIndex f j (coherentK0Class M) =
      (AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M.sheaf j).eval 0 := by
  change (coherentHilbertIndex f j (coherentK0Class M)).eval 0 = _
  rw [coherentHilbertIndex_class]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.KTheory.Projective
