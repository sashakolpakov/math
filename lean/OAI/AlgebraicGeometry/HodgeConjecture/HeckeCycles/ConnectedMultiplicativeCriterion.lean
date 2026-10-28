import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CharacterBasisCriterion
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CharacterCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRank
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks

/-! # Connected Multiplicative Criterion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConnectedMultiplicativeCriterion.CM

noncomputable section

/-! The original characters identify the connected factor with the
actual multiplicative block once its computed order is supplied. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NeutralGroup.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

variable {k : Type} [Field k] [IsAlgClosed k]
  (A : Grp (Over (Spec (.of k)))) [IsFinite A.X.hom] [IsCommMonObj A.X]
  (q : ℕ) [Fact q.Prime] [CharP k q] (n g : ℕ)

theorem multiplicative_factor
    (hkill : ∀ p : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X, p ^ (q ^ n) = 1)
    (e : TorsionCoordinateMaps.CM.Criterion.coordinates q n g ≃* (A ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))))
    (z : Spec (.of k)) (hrank : (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart A).X.hom.finrank z = (q ^ n) ^ g) :
    Nonempty (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart A ≅ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n g) := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  let : IsFinite (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart A).X.hom := HeckeCycles.Finite.NeutralGroup.CM.neutral_finite A
  let : IsCommMonObj (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart A).X :=
    Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative (HeckeCycles.Finite.GroupRetraction.CM.componentMap A)
  obtain ⟨R, hR, _, ⟨i⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart A)
  let : Module.Finite k R := hR
  let u : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n g ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q n g := MulEquiv.ulift
  let c := CharacterCoordinates.CM.coordinateCharactersEquiv k (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart A) R i
  let f : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n g →* GroupLike k R :=
    c.toMonoidHom.comp ((NeutralCharacters.CM.restrictionHom A).comp
      (e.toMonoidHom.comp u.toMonoidHom))
  have hf : Function.Injective f := c.injective.comp
    ((NeutralCharacters.CM.restrict_injective A q n hkill).comp (e.injective.comp u.injective))
  have hi : Module.finrank k R = (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart A).X.hom.finrank z := by
    let j : ((hopfSpec (.of k)).obj (.op R)).X ≅ (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart A).X := (Grp.forget _).mapIso i
    exact (AbelianScheme.CartierDuality.Rank.Construction.Schemes.spec_finrank_field k R z).symm.trans
      (AbelianScheme.CartierDuality.Rank.Construction.Schemes.overIso_finrank j z)
  have hc : Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n g) = (q ^ n) ^ g :=
    (Nat.card_congr u.toEquiv).trans
      ((TorsionCoordinateMaps.CM.Criterion.coordinates_card q n g (Fact.out : q.Prime).ne_zero).trans (pow_mul q n g))
  exact ⟨i.symm ≪≫ CharacterBasisCriterion.CM.diagonalizableIso k R
    (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n g) f hf (hi.trans (hrank.trans hc.symm))⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConnectedMultiplicativeCriterion.CM
