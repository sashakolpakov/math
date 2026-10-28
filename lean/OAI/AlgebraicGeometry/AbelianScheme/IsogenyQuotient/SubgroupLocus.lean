import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AgreementLocus

/-! # Subgroup Locus -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupLocus.Construction

/-!
Finite etaleness of the subgroup models and the block-support parameter
locus. Projectors on torsion may be lifted by O_E-endomorphisms; no
nontrivial idempotent endomorphism of the abelian scheme is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A]

/-- A finite locally free subgroup of etale n-torsion is itself etale.
This follows from its monomorphism into the base-changed torsion scheme. -/
theorem subgroup_model_etale
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model)
    (n : ℕ) (hkilled : F.KilledBy n)
    (h_TorsionQuotient : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) : Etale R.toBase.left := by
  let T := TorsionQuotient.SubgroupFunctor.torsionScheme A n
  let j : R.carrier ⟶ P ⊗ T := lift R.toBase (R.toTorsion hkilled)
  have hj : Mono j := by
    constructor
    intro X a b hab
    apply R.jointly_monic X a b
    · simpa only [j, Category.assoc, lift_fst] using
        congrArg (fun z => z ≫ fst P T) hab
    · have h := congrArg (fun z => z ≫ snd P T ≫ TorsionQuotient.SubgroupFunctor.torsionι A n) hab
      simpa only [j, Category.assoc, lift_snd_assoc, TorsionQuotient.SubgroupFunctor.RelativeSubgroup.Model.toTorsion_ι]
        using h
  have : Mono j := hj
  have : Mono j.left := inferInstance
  have : FormallyUnramified j.left := inferInstance
  have : Etale T.hom := h_TorsionQuotient
  have hfst : Etale (fst P T).left :=
    inferInstanceAs (Etale (pullback.fst P.hom T.hom))
  have hcomp : FormallyUnramified (j.left ≫ (fst P T).left) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance
  have heq : j.left ≫ (fst P T).left = R.toBase.left :=
    congrArg (fun z => z.left) (lift_fst R.toBase (R.toTorsion hkilled))
  have : FormallyUnramified R.toBase.left := heq ▸ hcomp
  have : Flat R.toBase.left := R.flat
  have : LocallyOfFinitePresentation R.toBase.left := R.finitePresentation
  exact Etale.of_formallyUnramified_of_flat R.toBase.left

/-- For a universal subgroup choice, support on one chosen torsion block
is represented by a finite etale clopen locus in its parameter scheme. -/
theorem finite_etale_block_support_locus
    [IsCommMonObj A]
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (F : TorsionQuotient.SubgroupFunctor.SubgroupChoice A n M P) (R : F.subgroup.Model)
    (projectorLift : A ⟶ A) [IsMonHom projectorLift]
    (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧
      Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) :
    ∃ U : P.left.Opens,
      IsFinite U.ι ∧ Etale U.ι ∧
      ∀ (T : Over S) (b : T ⟶ P),
        (∀ t : T.left, b.left t ∈ U) ↔
          SubgroupFunctor.Construction.SupportedOn (F.subgroup.baseChange b) projectorLift := by
  have : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := h_TorsionQuotient.1
  have : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := h_TorsionQuotient.2
  have : IsFinite R.toBase.left := R.finite
  have : Etale R.toBase.left := subgroup_model_etale F.subgroup R n F.killed h_TorsionQuotient.2
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι A n) := by
    unfold TorsionQuotient.SubgroupFunctor.torsionι
    exact equalizer.ι_mono (f := (𝟙 A : A ⟶ A) ^ n) (g := (1 : A ⟶ A))
  let a := R.toTorsion F.killed ≫ EtaleDetection.Construction.mapTorsion projectorLift n
  let b := R.toTorsion F.killed
  obtain ⟨U, hfinite, hetale, hU⟩ := AgreementLocus.Construction.finite_etale_agreement_locus R.toBase a b
  refine ⟨U, hfinite, hetale, ?_⟩
  intro T t
  rw [hU T t, SubgroupFunctor.Construction.supportedOn_iff_model_equation
    (F.subgroup.baseChange t) (R.baseChange t) projectorLift]
  rw [← cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι A n)]
  change _ ↔
    (pullback.fst R.toBase t ≫ R.toGroup) ≫ projectorLift =
      pullback.fst R.toBase t ≫ R.toGroup
  simp only [a, b, Category.assoc, EtaleDetection.Construction.mapTorsion_ι, TorsionQuotient.SubgroupFunctor.RelativeSubgroup.Model.toTorsion_ι]
  rw [← Category.assoc (R.toTorsion F.killed) (TorsionQuotient.SubgroupFunctor.torsionι A n) projectorLift,
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup.Model.toTorsion_ι]

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupLocus.Construction
