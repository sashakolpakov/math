import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierAnnihilatorComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingRestriction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedKernels

/-! # Opposite Cartier Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeCartierComparison

noncomputable section

/-! Transport the evaluation pairing through the original identification
of the opposite block with the Cartier dual. The resulting relative
annihilator is the independently constructed FrobeniusKernel opposite subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedKernels.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierPairing
  CartierAnnihilatorComparison

variable {K : Type u} [Field K]
variable {G H B : Grp (Over (Spec (.of K)))} {X : Over (Spec (.of K))}
variable (P : AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of K) G) (Q : AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of K) H)
variable (i : H ⟶ G) (d : B ≅ P.dualGroup)

def oppositePairing : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := G.X) (B := B.X)
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of K))).X) :=
  (CartierPairing.cartierPairing P).restrict (𝟙 G.X) d.hom.hom.hom

theorem opposite_annihilator_family :
    (oppositePairing P d).relativeAnnihilator (Kernel.Base.fixedKernelFamily (P := X) i.hom.hom) =
      Kernel.Base.fixedKernelFamily (P := X) (P.oppositeInclusion Q i d).hom.hom := by
  ext T t b
  have hmem : b ∈ ((oppositePairing P d).relativeAnnihilator
      (Kernel.Base.fixedKernelFamily (P := X) i.hom.hom)).points T t ↔
      b ≫ d.hom.hom.hom ∈ ((CartierPairing.cartierPairing P).relativeAnnihilator
        (Kernel.Base.fixedKernelFamily (P := X) i.hom.hom)).points T t := by
    constructor <;> intro hb U f a ha
    · have hv := hb U f a ha
      simpa only [oppositePairing, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue,
        Category.comp_id, Category.assoc] using hv
    · simpa only [oppositePairing, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue,
        Category.comp_id, Category.assoc] using hb U f a ha
  rw [hmem, CartierAnnihilatorComparison.cartier_annihilator_family P Q i]
  change (∃ a, a ≫ (P.annihilatorInclusion Q i).hom.hom = b ≫ d.hom.hom.hom) ↔
    ∃ a, a ≫ (P.oppositeInclusion Q i d).hom.hom = b
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    change a ≫ ((P.annihilatorInclusion Q i).hom.hom ≫ d.inv.hom.hom) = b
    have he := congrArg (fun z => z ≫ d.inv.hom.hom) ha
    have hd : d.hom.hom.hom ≫ d.inv.hom.hom = 𝟙 B.X :=
      ((Grp.forget _).mapIso d).hom_inv_id
    simpa only [Category.assoc, hd, Category.comp_id] using he
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    change a ≫ ((P.annihilatorInclusion Q i).hom.hom ≫ d.inv.hom.hom) = b at ha
    have he := congrArg (fun z => z ≫ d.hom.hom.hom) ha
    have hd : d.inv.hom.hom ≫ d.hom.hom.hom = 𝟙 P.dualGroup.X :=
      ((Grp.forget _).mapIso d).inv_hom_id
    simpa only [Category.assoc, hd, Category.comp_id] using he

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeCartierComparison
