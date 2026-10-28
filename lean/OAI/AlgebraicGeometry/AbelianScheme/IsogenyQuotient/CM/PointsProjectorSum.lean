import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel

/-! # Points Projector Sum -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction

noncomputable section

section

/-!
Adapt CMPoints's actual split residue coordinates and integral projector lifts
to the native IsogenyQuotient torsion blocks. Orthogonality and scalar restriction
are consequences of those coordinates, not extra quotient hypotheses.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

theorem l45_native_projectors_orthogonal (n : ℕ) (τ υ : Gal(E/ℚ)) (hne : τ ≠ υ) :
    Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (σ.map (j.projector iota hsplit n τ)) ≫
      Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (σ.map (j.projector iota hsplit n υ)) = 1 := by
  classical
  let eτ := j.projector iota hsplit n τ
  let eυ := j.projector iota hsplit n υ
  have hc : eυ * eτ - 0 ∈ Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} :
      Set (NumberField.RingOfIntegers E)) := by
    rw [← (hsplit n).2]
    change j.residueCoordinates iota n (eυ * eτ - 0) = 0
    rw [map_sub, map_mul, map_zero, sub_zero,
      j.projector_coordinates iota hsplit n υ, j.projector_coordinates iota hsplit n τ]
    ext ω
    by_cases hω : ω = υ
    · subst ω
      simp [hne]
    · simp [hω]
  have hh := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ (eυ * eτ) 0 (q ^ n)
    (by simpa only [Nat.cast_pow] using hc) (Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ n))
    (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n)) (Torsion.Groups.Construction.nativeTorsionInclusion_killed A.scheme (q ^ n))
  rw [σ.map_mul, σ.map_zero, MonObj.comp_one] at hh
  apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n))).mp
  rw [Category.assoc, Torsion.Groups.Construction.nativeTorsionMap_inclusion, ← Category.assoc,
    Torsion.Groups.Construction.nativeTorsionMap_inclusion, Category.assoc, MonObj.one_comp]
  exact hh

theorem l45_native_projector_scalar (n : ℕ) (τ : Gal(E/ℚ)) (a : NumberField.RingOfIntegers E) :
    OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) ≫ σ.map a =
      (OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ))) ^
        ((j.residueCharacter iota τ n a).val : ℤ) := by
  have hx := (PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit A σ n τ _
    (OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)))).mpr
      ⟨OppositeKernel.Construction.torsionBlockInclusion_killed _ _, OppositeKernel.Construction.torsionBlockInclusion_supported _ _⟩
  simpa only [zpow_natCast, PELModuli.CMPoints.Arithmetic.QadicChoice.residueCharacter, RingHom.comp_apply] using hx.2 a

def l45NativeBlockPointsEquiv (n : ℕ) (τ : Gal(E/ℚ)) (T : Over S) :
    (T ⟶ OppositeKernel.Construction.torsionBlock (q ^ n) (σ.map (j.projector iota hsplit n τ))) ≃*
      PELModuli.CMPoints.BlocksProjectors.blockPoints A σ (j.localCharacter iota τ) n T where
  toFun f := ⟨f ≫ OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)), by
    apply (PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit A σ n τ T _).mpr
    constructor
    · rw [← MonObj.comp_pow, OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]
    · rw [Category.assoc, OppositeKernel.Construction.torsionBlockInclusion_supported]⟩
  invFun x := OppositeKernel.Construction.torsionBlockLift (q ^ n) (σ.map (j.projector iota hsplit n τ)) x.val
    ((PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit A σ n τ T x.val).mp x.property).1
    ((PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit A σ n τ T x.val).mp x.property).2
  left_inv f := by
    apply (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)))).mp
    exact OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _
  right_inv x := Subtype.ext (OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _)
  map_mul' f g := Subtype.ext (MonObj.mul_comp f g _)

def l45NativeBlockRepresentable (n : ℕ) (τ : Gal(E/ℚ)) :
    (PELModuli.CMPoints.BlocksProjectors.blockFunctor A σ (j.localCharacter iota τ) n ⋙ forget GrpCat).RepresentableBy
      (OppositeKernel.Construction.torsionBlock (q ^ n) (σ.map (j.projector iota hsplit n τ))) where
  homEquiv := (l45NativeBlockPointsEquiv j iota hsplit A σ n τ _).toEquiv
  homEquiv_comp f a := Subtype.ext (Category.assoc f a _)

/-- The native IsogenyQuotient block and CMPoints's equalizer represent the same actual
character subfunctor on every test scheme. -/
def l45NativeBlockIso (n : ℕ) (τ : Gal(E/ℚ)) :
    OppositeKernel.Construction.torsionBlock (q ^ n) (σ.map (j.projector iota hsplit n τ)) ≅
      PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A σ (q ^ n) (j.projector iota hsplit n τ) :=
  (l45NativeBlockRepresentable j iota hsplit A σ n τ).uniqueUpToIso
    (PELModuli.CMPoints.BlocksProjectors.splitBlockRepresentable j iota hsplit A σ n τ)

end

/-!
The lifted residue idempotents form a complete decomposition on the
actual torsion scheme. Their sum is proved to be the identity from the
split residue coordinates, without assuming a torsion-product splitting.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

theorem integral_action_sum_on_points {O : Type*} [CommRing O]
    {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
    {I : Type*} (s : Finset I) (a : I → O) (T : Over S) (x : T ⟶ A.scheme) :
    x ≫ σ.map (∑ i ∈ s, a i) = ∏ i ∈ s, x ≫ σ.map (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [σ.map_zero, MonObj.comp_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, σ.map_add, MonObj.comp_mul, ih, Finset.prod_insert hi]

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

theorem l45_projectors_sum_on_torsion (n : ℕ) (T : Over S)
    (x : T ⟶ A.scheme) (hx : x ^ (q ^ n) = 1) :
    (∏ τ : Gal(E/ℚ), x ≫ σ.map (j.projector iota hsplit n τ)) = x := by
  classical
  have hcoord : j.residueCoordinates iota n (∑ τ : Gal(E/ℚ), j.projector iota hsplit n τ) = 1 := by
    rw [map_sum]
    ext υ
    simp [j.projector_coordinates, Pi.single_apply]
  have hc : (∑ τ : Gal(E/ℚ), j.projector iota hsplit n τ) - 1 ∈
      Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)) := by
    rw [← (hsplit n).2]
    change j.residueCoordinates iota n ((∑ τ : Gal(E/ℚ), j.projector iota hsplit n τ) - 1) = 0
    rw [map_sub, hcoord, map_one, sub_self]
  have he := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ _ 1 (q ^ n)
    (by simpa only [Nat.cast_pow] using hc) T x hx
  rw [integral_action_sum_on_points, σ.map_one, Category.comp_id] at he
  exact he

/-- Completeness of the native projectors, as an equality of actual
endomorphisms of the entire torsion group scheme. -/
theorem l45_native_projectors_complete (n : ℕ) :
    (∏ τ : Gal(E/ℚ), Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (σ.map (j.projector iota hsplit n τ))) =
      𝟙 (Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ n)) := by
  apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n))).mp
  rw [Category.id_comp]
  calc
    (∏ τ : Gal(E/ℚ), Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (σ.map (j.projector iota hsplit n τ))) ≫
        Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n) =
      ∏ τ : Gal(E/ℚ), Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (σ.map (j.projector iota hsplit n τ)) ≫
        Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n) :=
      map_prod (IsMonHom.monoidHom (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n))
        (Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ n))) _ _
    _ = ∏ τ : Gal(E/ℚ), Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n) ≫
        σ.map (j.projector iota hsplit n τ) :=
      Finset.prod_congr rfl (fun τ _ => Torsion.Groups.Construction.nativeTorsionMap_inclusion (q ^ n) _)
    _ = Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n) :=
      l45_projectors_sum_on_torsion j iota hsplit A σ n _ _ (Torsion.Groups.Construction.nativeTorsionInclusion_killed _ _)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction
