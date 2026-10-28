import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockGroups
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Annihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Product

/-! # Opposite Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel.Construction

noncomputable section

/-!
Construct the opposite annihilator and the paired kernel on the original
abelian scheme. All subgroup models and all embeddings are produced from
the torsion blocks and the actual scheme pairing. Orthogonality of the
local projectors proves the injectivity needed for the product model.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] [IsCommMonObj A]

abbrev torsionBlock (n : ℕ) (p : A ⟶ A) [IsMonHom p] : Over S :=
  BlockGroups.Construction.fixedPointScheme (Torsion.Groups.Construction.nativeTorsionMap n p)

def torsionBlockInclusion (n : ℕ) (p : A ⟶ A) [IsMonHom p] : torsionBlock n p ⟶ A :=
  BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n p) ≫ Torsion.Groups.Construction.nativeTorsionInclusion A n

instance torsionBlockInclusion_isMonHom (n : ℕ) (p : A ⟶ A) [IsMonHom p] :
    IsMonHom (torsionBlockInclusion n p) := by
  unfold torsionBlockInclusion
  infer_instance

instance torsionBlockInclusion_mono (n : ℕ) (p : A ⟶ A) [IsMonHom p] :
    Mono (torsionBlockInclusion n p) := by
  unfold torsionBlockInclusion
  infer_instance

theorem torsionBlockInclusion_killed (n : ℕ) (p : A ⟶ A) [IsMonHom p] :
    (torsionBlockInclusion n p) ^ n = 1 := by
  rw [torsionBlockInclusion, ← MonObj.comp_pow, Torsion.Groups.Construction.nativeTorsionInclusion_killed, MonObj.comp_one]

theorem torsionBlockInclusion_supported (n : ℕ) (p : A ⟶ A) [IsMonHom p] :
    torsionBlockInclusion n p ≫ p = torsionBlockInclusion n p := by
  rw [torsionBlockInclusion, Category.assoc, ← Torsion.Groups.Construction.nativeTorsionMap_inclusion,
    ← Category.assoc, BlockGroups.Construction.fixedPointInclusion_fixed]

def torsionBlockLift (n : ℕ) (p : A ⟶ A) [IsMonHom p] {X : Over S}
    (x : X ⟶ A) (hxn : x ^ n = 1) (hxp : x ≫ p = x) : X ⟶ torsionBlock n p :=
  BlockGroups.Construction.fixedPointLift (Torsion.Groups.Construction.nativeTorsionMap n p) (Torsion.Groups.Construction.nativeTorsionLift A n x hxn) (by
    apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion A n)).mp
    rw [Category.assoc, Torsion.Groups.Construction.nativeTorsionMap_inclusion, ← Category.assoc,
      Torsion.Groups.Construction.nativeTorsionLift_inclusion, hxp])

@[simp]
theorem torsionBlockLift_inclusion (n : ℕ) (p : A ⟶ A) [IsMonHom p] {X : Over S}
    (x : X ⟶ A) (hxn : x ^ n = 1) (hxp : x ≫ p = x) :
    torsionBlockLift n p x hxn hxp ≫ torsionBlockInclusion n p = x := by
  rw [torsionBlockInclusion, ← Category.assoc, torsionBlockLift,
    BlockGroups.Construction.fixedPointLift_inclusion, Torsion.Groups.Construction.nativeTorsionLift_inclusion]

theorem torsionBlock_finite_etale
    (n : ℕ) (p : A ⟶ A) [IsMonHom p]
    (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧ Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) :
    IsFinite (torsionBlock n p).hom ∧ Etale (torsionBlock n p).hom := by
  obtain ⟨hf, he⟩ := Torsion.Groups.Construction.nativeTorsionScheme_finite_etale A n h_TorsionQuotient
  have : IsFinite (Torsion.Groups.Construction.nativeTorsionScheme A n).hom := hf
  have : Etale (Torsion.Groups.Construction.nativeTorsionScheme A n).hom := he
  exact BlockGroups.Construction.fixedPointScheme_finite_etale (Torsion.Groups.Construction.nativeTorsionMap n p)

theorem torsionBlockInclusion_separated
    (n : ℕ) (p q : A ⟶ A) [IsMonHom p] [IsMonHom q]
    (hpq : Torsion.Groups.Construction.nativeTorsionMap n q ≫ Torsion.Groups.Construction.nativeTorsionMap n p = 1) :
    torsionBlockInclusion n q ≫ p = 1 := by
  have hsep : BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n q) ≫ Torsion.Groups.Construction.nativeTorsionMap n p = 1 := by
    calc
      _ = (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap n q) ≫ Torsion.Groups.Construction.nativeTorsionMap n q) ≫
          Torsion.Groups.Construction.nativeTorsionMap n p :=
        congrArg (fun z => z ≫ Torsion.Groups.Construction.nativeTorsionMap n p) (BlockGroups.Construction.fixedPointInclusion_fixed _).symm
      _ = 1 := by rw [Category.assoc, hpq, MonObj.comp_one]
  rw [torsionBlockInclusion, Category.assoc, ← Torsion.Groups.Construction.nativeTorsionMap_inclusion,
    ← Category.assoc, hsep, MonObj.one_comp]

variable {P : Over S}

def supportedTorsionBlock_model
    (n : ℕ) (p : A ⟶ A) [IsMonHom p]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model)
    (hkilled : F.KilledBy n) (hsupport : SubgroupFunctor.Construction.SupportedOn F p) :
    (SubgroupTransport.Construction.relativeSubgroupPullback (torsionBlockInclusion n p) F).Model :=
  SubgroupTransport.Construction.relativeSubgroupPullback_model (torsionBlockInclusion n p) F R
    (torsionBlockLift n p R.toGroup (R.toGroup_pow_eq_one hkilled)
      ((SubgroupFunctor.Construction.supportedOn_iff_model_equation F R p).mp hsupport))
    (torsionBlockLift_inclusion _ _ _ _ _)

theorem supportedTorsionBlock_image
    (n : ℕ) (p : A ⟶ A) [IsMonHom p]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (hkilled : F.KilledBy n) (hsupport : SubgroupFunctor.Construction.SupportedOn F p) :
    SubgroupTransport.Construction.relativeSubgroupImage (torsionBlockInclusion n p)
      (SubgroupTransport.Construction.relativeSubgroupPullback (torsionBlockInclusion n p) F) = F := by
  apply SubgroupTransport.Construction.relativeSubgroupPullback_image
  intro X t x hx
  exact ⟨torsionBlockLift n p x (hkilled X t x hx) (hsupport X t x hx),
    torsionBlockLift_inclusion _ _ _ _ _⟩

variable (n : ℕ) (p q : A ⟶ A) [IsMonHom p] [IsMonHom q]
variable {W : Over S} [GrpObj W]
variable (e : Annihilator.Construction.SchemeBicharacter (A := torsionBlock n p) (B := torsionBlock n q) (W := W))

/-- The opposite subgroup is the annihilator, embedded into the original
abelian scheme through the opposite torsion block. -/
def oppositeKernel (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P :=
  SubgroupTransport.Construction.relativeSubgroupImage (torsionBlockInclusion n q)
    (e.relativeAnnihilator (SubgroupTransport.Construction.relativeSubgroupPullback (torsionBlockInclusion n p) F))

theorem oppositeKernel_baseChange (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    {Q : Over S} (b : Q ⟶ P) :
    (oppositeKernel n p q e F).baseChange b = oppositeKernel n p q e (F.baseChange b) := by
  rw [oppositeKernel, SubgroupTransport.Construction.relativeSubgroupImage_baseChange,
    Annihilator.Construction.SchemeBicharacter.relativeAnnihilator_baseChange, SubgroupTransport.Construction.relativeSubgroupPullback_baseChange]
  rfl

/-- Produce the opposite subgroup and the full paired kernel as actual
finite locally free subgroups, killed by the one common multiplier n. -/
theorem oppositeKernel_and_product_models
    [Etale W.hom] [IsSeparated W.hom]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model)
    (hkilled : F.KilledBy n) (hsupport : SubgroupFunctor.Construction.SupportedOn F p)
    (hpq : Torsion.Groups.Construction.nativeTorsionMap n q ≫ Torsion.Groups.Construction.nativeTorsionMap n p = 1)
    (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧ Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) :
    Nonempty (oppositeKernel n p q e F).Model ∧
      (oppositeKernel n p q e F).KilledBy n ∧
      Nonempty (Kernel.Product.Construction.relativeKernelProduct F (oppositeKernel n p q e F)).Model ∧
      (Kernel.Product.Construction.relativeKernelProduct F (oppositeKernel n p q e F)).KilledBy n := by
  let FB := SubgroupTransport.Construction.relativeSubgroupPullback (torsionBlockInclusion n p) F
  let RB := supportedTorsionBlock_model n p F R hkilled hsupport
  have : Etale RB.toBase.left := SubgroupLocus.Construction.subgroup_model_etale F R n hkilled h_TorsionQuotient.2
  obtain ⟨hqfinite, hqetale⟩ := torsionBlock_finite_etale n q h_TorsionQuotient
  have : IsFinite (torsionBlock n q).hom := hqfinite
  have : Etale (torsionBlock n q).hom := hqetale
  obtain ⟨Q⟩ := e.relativeAnnihilator_has_model FB RB
  let G := oppositeKernel n p q e F
  let RG : G.Model := SubgroupTransport.Construction.relativeSubgroupImage_model (torsionBlockInclusion n q)
    (e.relativeAnnihilator FB) Q
  have hGkilled : G.KilledBy n := by
    intro X t x hx
    obtain ⟨y, _, rfl⟩ := hx
    change (y ≫ torsionBlockInclusion n q) ^ n = 1
    rw [← MonObj.comp_pow, torsionBlockInclusion_killed, MonObj.comp_one]
  have hRG : RG.toGroup ≫ p = 1 := by
    change (Q.toGroup ≫ torsionBlockInclusion n q) ≫ p = 1
    rw [Category.assoc, torsionBlockInclusion_separated n p q hpq, MonObj.comp_one]
  refine ⟨⟨RG⟩, hGkilled, ?_, Kernel.Product.Construction.relativeKernelProduct_killed F G n hkilled hGkilled⟩
  exact ⟨Kernel.Product.Construction.relativeKernelProduct_model F G R RG p
    ((SubgroupFunctor.Construction.supportedOn_iff_model_equation F R p).mp hsupport) hRG⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel.Construction
