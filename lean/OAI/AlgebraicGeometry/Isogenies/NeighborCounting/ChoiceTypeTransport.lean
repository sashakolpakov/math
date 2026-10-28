import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor

/-! # Choice Type Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceTypeTransport

noncomputable section

/-! Change only the abstract elementary-group presentation of an
original supported choice. The relative subgroup, its model existence,
and every ambient membership condition remain the same. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction

variable {S : Scheme} {A P : Over S} [GrpObj A] (n : ℕ)
  {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [Module (ZMod n) M] [Module (ZMod n) N] [Finite M] [Finite N]
  (p : A ⟶ A) (e : M ≃+ N)

def supportedChoiceTypeMap (F : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A n M p P) : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A n N p P :=
  ⟨{
    subgroup := F.val.subgroup
    killed := F.val.killed
    moduleType := fun K _ _ s t =>
      (F.val.moduleType K s t).map (fun h => h.trans e.toMultiplicative)
    geometric := F.val.geometric }, F.property⟩

def supportedChoiceTypeEquiv : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A n M p P ≃ AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A n N p P where
  toFun := supportedChoiceTypeMap n p e
  invFun := supportedChoiceTypeMap n p e.symm
  left_inv _ := Subtype.ext (AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext rfl)
  right_inv _ := Subtype.ext (AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext rfl)

theorem supportedChoiceTypeEquiv_subgroup (F : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A n M p P) :
    (supportedChoiceTypeEquiv n p e F).val.subgroup = F.val.subgroup := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceTypeTransport
