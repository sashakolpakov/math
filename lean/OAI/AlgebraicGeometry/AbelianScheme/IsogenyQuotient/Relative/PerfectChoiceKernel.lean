import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectSplitPairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DoubleAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceIsotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplication

/-! # Perfect Choice Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PerfectChoiceKernel.Construction

noncomputable section

/-!
The exact quotient kernel of an arbitrary family of supported choices
is self-annihilating for the original perfect alternating source pairing.
Actual CartierDuality duality supplies the double-annihilator equations on every
test scheme; TorsionQuotient supplies all finite torsion-block geometry.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u

theorem supported_relative_double_annihilator_from_perfect_pairing
    {K : Type u} [Field K] [CharZero K] {S : Scheme.{u}}
    (base : S ⟶ Spec (.of K)) {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) {P : Over S}
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (R : F.Model)
    (n : ℕ) (hn : 0 < n) (p r : A.scheme ⟶ A.scheme) [IsMonHom p] [IsMonHom r]
    (hkilled : F.KilledBy n) (hsupport : SubgroupFunctor.Construction.SupportedOn F p)
    (e : Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n p) (B := OppositeKernel.Construction.torsionBlock n r)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) (he : e.toSheafPairing.IsPerfect) :
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n p) F
    e.flip.relativeAnnihilator (e.relativeAnnihilator H) = H := by
  have hblock := OppositeKernel.Construction.torsionBlock_finite_etale n p
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) base n hn Torsion.Construction.verified_TorsionQuotientInput)
  let : IsFinite (OppositeKernel.Construction.torsionBlock n p).hom := hblock.1
  let : Etale (OppositeKernel.Construction.torsionBlock n p).hom := hblock.2
  exact DoubleAnnihilator.Construction.relative_double_annihilator_from_perfect_pairing (Grp.mk (OppositeKernel.Construction.torsionBlock n p))
    (Grp.mk (OppositeKernel.Construction.torsionBlock n r)) P (SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n p) F)
    (OppositeKernel.Construction.supportedTorsionBlock_model n p F R hkilled hsupport) e he

theorem relativeChoiceFullKernel_self_annihilating_from_perfect_source
    {K : Type u} [Field K] [CharZero K] {S : Scheme.{u}}
    (base : S ⟶ Spec (.of K)) {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) {P : Over S}
    (n s : ℕ) (hn : 0 < n) (M : Fin s → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
    (p r : Fin s → (A.scheme ⟶ A.scheme)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (r i)]
    (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A.scheme n (M i) (p i) P)
    (horth : ∀ i j : ChoiceKernel.Construction.KernelIndex s, i ≠ j →
      ChoiceIsotropy.Construction.choiceTorsionProjector n s p r i ≫ ChoiceIsotropy.Construction.choiceTorsionProjector n s p r j = 1)
    (hcomplete : (∏ i, ChoiceIsotropy.Construction.choiceTorsionProjector n s p r i) = 𝟙 (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n))
    (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (hb : b.toSheafPairing.IsPerfect)
    (halt : ∀ (X : Over S) (x : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n), b.pairValue x x = 1)
    (hadjoint : ∀ (i : ChoiceKernel.Construction.KernelIndex s) (X : Over S) (x y : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n),
      b.pairValue (x ≫ ChoiceIsotropy.Construction.choiceTorsionProjector n s p r i) y =
        b.pairValue x (y ≫ ChoiceIsotropy.Construction.choiceTorsionProjector n s p r (Sum.swap i))) :
    let e : ∀ i : Fin s, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i))
        (B := OppositeKernel.Construction.torsionBlock n (r i)) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
      SourcePairingFormula.Construction.sourceBlockPairing (ChoiceIsotropy.Construction.choiceTorsionProjector n s p r) b
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) (ChoiceKernel.Construction.choiceFullKernel n s M p r e U)
    b.relativeAnnihilator H = H := by
  let e : ∀ i : Fin s, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i))
      (B := OppositeKernel.Construction.torsionBlock n (r i)) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
    SourcePairingFormula.Construction.sourceBlockPairing (ChoiceIsotropy.Construction.choiceTorsionProjector n s p r) b
  have hdouble (i : Fin s) : (e i).flip.relativeAnnihilator
      ((e i).relativeAnnihilator
        (SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n (p i)) (U i).val.subgroup)) =
      SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n (p i)) (U i).val.subgroup :=
    supported_relative_double_annihilator_from_perfect_pairing base A (U i).val.subgroup
      (Classical.choice (U i).val.geometric) n hn (p i) (r i) (U i).val.killed (U i).property (e i)
      (PerfectSplitPairing.Construction.sourceBlockPairing_isPerfect _ horth hcomplete b hb hadjoint i)
  have he : b = ChoiceIsotropy.Construction.choiceTorsionPairing n s p r e horth hcomplete :=
    SourcePairingFormula.Construction.sourcePairing_eq_fullSplit _ horth hcomplete b halt hadjoint
  exact (congrArg (fun c : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) =>
      c.relativeAnnihilator
        (SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) (ChoiceKernel.Construction.choiceFullKernel n s M p r e U))) he).trans
    (ChoiceIsotropy.Construction.choiceFullKernel_self_annihilating_of_CartierDuality n s M p r e U horth hcomplete hdouble)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PerfectChoiceKernel.Construction
