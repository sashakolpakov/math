import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel

/-! # Supported Block Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedBlockChoices.Construction

noncomputable section

/-!
Supported subgroup choices in the abelian scheme are the same choices
inside its native torsion block. The finite locally free model and all
geometric type conditions are transported along the actual inclusion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  (n : ℕ) (p : A ⟶ A) [IsMonHom p]

def supportedBlockPointsEquiv (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (hk : F.KilledBy n) (hp : SubgroupFunctor.Construction.SupportedOn F p) (X : Over S) (t : X ⟶ P) :
    (SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n p) F).points X t ≃* F.points X t where
  toFun y := ⟨y.val ≫ OppositeKernel.Construction.torsionBlockInclusion n p, y.property⟩
  invFun x := ⟨OppositeKernel.Construction.torsionBlockLift n p x.val (hk X t x.val x.property) (hp X t x.val x.property), by
    change OppositeKernel.Construction.torsionBlockLift n p x.val _ _ ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈ F.points X t
    rw [OppositeKernel.Construction.torsionBlockLift_inclusion]
    exact x.property⟩
  left_inv y := by
    apply Subtype.ext
    apply (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion n p)).mp
    exact OppositeKernel.Construction.torsionBlockLift_inclusion n p (y.val ≫ OppositeKernel.Construction.torsionBlockInclusion n p)
      (hk X t _ y.property) (hp X t _ y.property)
  right_inv x := Subtype.ext (OppositeKernel.Construction.torsionBlockLift_inclusion n p x.val
    (hk X t x.val x.property) (hp X t x.val x.property))
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val _)

theorem torsionBlock_identity_killed : (𝟙 (OppositeKernel.Construction.torsionBlock n p)) ^ n = 1 := by
  apply (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion n p)).mp
  rw [MonObj.pow_comp, Category.id_comp, OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.one_comp]

variable (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]

def supportedChoiceToBlock (F : SubgroupFunctor.Construction.SupportedChoice A n M p P) :
    TorsionQuotient.SubgroupFunctor.SubgroupChoice (OppositeKernel.Construction.torsionBlock n p) n M P where
  subgroup := SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n p) F.val.subgroup
  killed X t x _ := by
    have hx := congrArg (fun f : OppositeKernel.Construction.torsionBlock n p ⟶ OppositeKernel.Construction.torsionBlock n p => x ≫ f)
      (torsionBlock_identity_killed n p)
    simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using hx
  moduleType := by
    intro K _ _ s t
    obtain ⟨e⟩ := F.val.moduleType K s t
    exact ⟨(supportedBlockPointsEquiv n p F.val.subgroup F.val.killed F.property _ t).trans e⟩
  geometric := F.val.geometric.elim fun R =>
    ⟨OppositeKernel.Construction.supportedTorsionBlock_model n p F.val.subgroup R F.val.killed F.property⟩

def blockChoiceToSupported (F : TorsionQuotient.SubgroupFunctor.SubgroupChoice (OppositeKernel.Construction.torsionBlock n p) n M P) :
    SubgroupFunctor.Construction.SupportedChoice A n M p P := by
  let G := SubgroupTransport.Construction.relativeSubgroupImage (OppositeKernel.Construction.torsionBlockInclusion n p) F.subgroup
  refine ⟨⟨G, ?_, ?_, ?_⟩, ?_⟩
  · intro X t x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (y ≫ OppositeKernel.Construction.torsionBlockInclusion n p) ^ n = 1
    rw [← MonObj.pow_comp, F.killed X t y hy, MonObj.one_comp]
  · intro K _ _ s t
    obtain ⟨e⟩ := F.moduleType K s t
    let eF := (F.subgroup.points (Over.mk s) t).equivMapOfInjective
      (IsMonHom.monoidHom (OppositeKernel.Construction.torsionBlockInclusion n p) (Over.mk s))
      (fun x y hxy => (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion n p)).mp hxy)
    exact ⟨eF.symm.trans e⟩
  · exact F.geometric.elim fun R => ⟨SubgroupTransport.Construction.relativeSubgroupImage_model (OppositeKernel.Construction.torsionBlockInclusion n p) F.subgroup R⟩
  · intro X t x hx
    obtain ⟨y, _, rfl⟩ := hx
    change (y ≫ OppositeKernel.Construction.torsionBlockInclusion n p) ≫ p = y ≫ OppositeKernel.Construction.torsionBlockInclusion n p
    rw [Category.assoc, OppositeKernel.Construction.torsionBlockInclusion_supported]

def supportedChoiceBlockEquiv :
    SubgroupFunctor.Construction.SupportedChoice A n M p P ≃ TorsionQuotient.SubgroupFunctor.SubgroupChoice (OppositeKernel.Construction.torsionBlock n p) n M P where
  toFun := supportedChoiceToBlock n p M
  invFun := blockChoiceToSupported n p M
  left_inv F := by
    apply Subtype.ext
    apply TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext
    exact OppositeKernel.Construction.supportedTorsionBlock_image n p F.val.subgroup F.val.killed F.property
  right_inv F := by
    apply TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext
    ext X t x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have he : y = x := (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion n p)).mp hxy
      exact he ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedBlockChoices.Construction
