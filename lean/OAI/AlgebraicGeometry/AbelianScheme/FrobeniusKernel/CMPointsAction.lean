import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplittingPoints

/-! # CM Points Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAction.Construction

noncomputable section

section

/-! Explicit coordinates of the full embedded native paired subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin s, PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

abbrev l45PairedChosenFamily (v : Fin s) :=
  (P v).pairedKernel (H v).coordinates (H v).inclusion

abbrev l45ChosenOppositeInclusion (v : Fin s) :=
  (P v).oppositeInclusion (H v).coordinates (H v).inclusion
    (CMPointsAt.Construction.l45PairingAtLevel j iota hsplit PEL ρ (labels (v, false)) (labels (v, true)) (hdual v) n (P v))

abbrev l45FullChosenBlockMap :=
  BlockProducts.Construction.groupBlockProductMap s (l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H)
    (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit PEL.abelian ρ n s labels)
    (fun v => (H v).inclusion ⊗ₘ l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual v)

def l45FullChosenPointBlocks (T : Over (Spec (.of k)))
    (a : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X) :=
  CMPointsSplitting.Construction.l45FullBlockCharacters j iota hsplit PEL.abelian ρ n s labels T
    (a ≫ (l45FullChosenBlockMap j iota hsplit PEL ρ n s labels P H hdual).hom.hom)

local instance : Fintype Gal(E/ℚ) := Fintype.ofFinite _

theorem l45FullChosenKernelInclusion_point (T : Over (Spec (.of k)))
    (a : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X) :
    a ≫ CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual =
      ∏ τ : Gal(E/ℚ), (l45FullChosenPointBlocks j iota hsplit PEL ρ n s labels P H hdual T a τ).val := by
  let f := (l45FullChosenBlockMap j iota hsplit PEL ρ n s labels P H hdual).hom.hom
  let b := (CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit PEL.abelian ρ n s labels).inv.hom.hom
  change a ≫ ((f ≫ b) ≫ PEL.abelian.torsionInclusion (q ^ n)) = _
  exact (Category.assoc a (f ≫ b) (PEL.abelian.torsionInclusion (q ^ n))).symm.trans
    ((congrArg (fun z => z ≫ PEL.abelian.torsionInclusion (q ^ n))
      (Category.assoc a f b).symm).trans
        (CMPointsSplittingPoints.Construction.l45FullTorsionSplitting_inv_inclusion j iota hsplit PEL.abelian ρ n s labels T (a ≫ f)))

theorem l45FullChosenPointBlocks_false (T : Over (Spec (.of k)))
    (a : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X) (v : Fin s) :
    l45FullChosenPointBlocks j iota hsplit PEL ρ n s labels P H hdual T a (labels (v, false)) =
      (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PEL.abelian ρ n (labels (v, false))).hom.app (op T)
        ((ProductPoints.Construction.groupBlockProductPointsEquiv s (l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H)
          T a v ≫ fst _ _) ≫ (H v).inclusion.hom.hom) := by
  let D := l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H
  let B := CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit PEL.abelian ρ n s labels
  let f := fun v => (H v).inclusion ⊗ₘ
    l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual v
  have hm := ProductPoints.Construction.groupBlockProductPointsEquiv_map s D B f T a v
  let b := ProductPoints.Construction.groupBlockProductPointsEquiv s D T a v
  have hp := (congrArg (fun z => z ≫ fst
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n).X
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, true)) n).X) hm).trans
    ((Category.assoc b (f v).hom.hom (fst _ _)).trans
      ((congrArg (fun z => b ≫ z) (tensorHom_fst (H v).inclusion.hom.hom
        (l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual v).hom.hom)).trans
          (Category.assoc b (fst _ _) (H v).inclusion.hom.hom).symm))
  exact (CMPointsSplitting.Construction.l45FullBlockCharacters_false j iota hsplit PEL.abelian ρ n s labels T
    (a ≫ (l45FullChosenBlockMap j iota hsplit PEL ρ n s labels P H hdual).hom.hom) v).trans
      (congrArg ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PEL.abelian ρ n (labels (v, false))).hom.app (op T)) hp)

theorem l45FullChosenPointBlocks_true (T : Over (Spec (.of k)))
    (a : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X) (v : Fin s) :
    l45FullChosenPointBlocks j iota hsplit PEL ρ n s labels P H hdual T a (labels (v, true)) =
      (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PEL.abelian ρ n (labels (v, true))).hom.app (op T)
        ((ProductPoints.Construction.groupBlockProductPointsEquiv s (l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H)
          T a v ≫ snd _ _) ≫
            (l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual v).hom.hom) := by
  let D := l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H
  let B := CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit PEL.abelian ρ n s labels
  let f := fun v => (H v).inclusion ⊗ₘ
    l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual v
  have hm := ProductPoints.Construction.groupBlockProductPointsEquiv_map s D B f T a v
  let b := ProductPoints.Construction.groupBlockProductPointsEquiv s D T a v
  have hp := (congrArg (fun z => z ≫ snd
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n).X
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, true)) n).X) hm).trans
    ((Category.assoc b (f v).hom.hom (snd _ _)).trans
      ((congrArg (fun z => b ≫ z) (tensorHom_snd (H v).inclusion.hom.hom
        (l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual v).hom.hom)).trans
          (Category.assoc b (snd _ _)
            (l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual v).hom.hom).symm))
  exact (CMPointsSplitting.Construction.l45FullBlockCharacters_true j iota hsplit PEL.abelian ρ n s labels T
    (a ≫ (l45FullChosenBlockMap j iota hsplit PEL ρ n s labels P H hdual).hom.hom) v).trans
      (congrArg ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PEL.abelian ρ n (labels (v, true))).hom.app (op T)) hp)

end

/-!
The full native paired kernel is stable under the integral action.
Each chosen and opposite factor is a subgroup of its actual scalar
block; their proved stability assembles on arbitrary test schemes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin s, PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

local instance : Fintype Gal(E/ℚ) := Fintype.ofFinite _

theorem l45FullChosenKernel_stable (r : NumberField.RingOfIntegers E)
    (T : Over (Spec (.of k)))
    (a : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X) :
    ∃ a' : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X,
      a' ≫ CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual =
        (a ≫ CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual) ≫ ρ.map r := by
  classical
  let D := l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H
  let ec := ProductPoints.Construction.groupBlockProductPointsEquiv s D T
  let J := fun v => (P v).annihilatorGroup (H v).coordinates (H v).inclusion
  let f := l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual
  have h0 := fun v => CMPointsAt.Construction.l45BlockSubgroup_stable j iota hsplit PEL.abelian ρ n
    (labels (v, false)) (H v).group (H v).inclusion r T (ec a v ≫ fst (H v).group.X (J v).X)
  have h1 := fun v => CMPointsAt.Construction.l45BlockSubgroup_stable j iota hsplit PEL.abelian ρ n
    (labels (v, true)) (J v) (f v) r T (ec a v ≫ snd (H v).group.X (J v).X)
  choose b0 hb0 using h0
  choose b1 hb1 using h1
  let a' := ec.symm (fun v => lift (b0 v) (b1 v))
  have hcoord (v : Fin s) : ec a' v = lift (b0 v) (b1 v) :=
    congrFun (ec.apply_symm_apply _) v
  have hc : ∀ τ : Gal(E/ℚ),
      (l45FullChosenPointBlocks j iota hsplit PEL ρ n s labels P H hdual T a' τ).val =
        (l45FullChosenPointBlocks j iota hsplit PEL ρ n s labels P H hdual T a τ).val ≫ ρ.map r := by
    intro τ
    obtain ⟨⟨v, b⟩, rfl⟩ := labels.surjective τ
    cases b with
    | false =>
      let inc := (H v).inclusion.hom.hom
      let bi := CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, false))
      have hp : ec a' v ≫ fst (H v).group.X (J v).X = b0 v :=
        (congrArg (fun z => z ≫ fst (H v).group.X (J v).X) (hcoord v)).trans (lift_fst _ _)
      have hs := congrArg Subtype.val
        (l45FullChosenPointBlocks_false j iota hsplit PEL ρ n s labels P H hdual T a v)
      have ht := congrArg Subtype.val
        (l45FullChosenPointBlocks_false j iota hsplit PEL ρ n s labels P H hdual T a' v)
      exact ht.trans ((congrArg (fun z => (z ≫ inc) ≫ bi) hp).trans
        ((Category.assoc (b0 v) inc bi).trans ((hb0 v).trans
          (congrArg (fun z => z ≫ ρ.map r)
            ((Category.assoc (ec a v ≫ fst (H v).group.X (J v).X) inc bi).symm.trans hs.symm)))))
    | true =>
      let inc := (f v).hom.hom
      let bi := CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, true))
      have hp : ec a' v ≫ snd (H v).group.X (J v).X = b1 v :=
        (congrArg (fun z => z ≫ snd (H v).group.X (J v).X) (hcoord v)).trans (lift_snd _ _)
      have hs := congrArg Subtype.val
        (l45FullChosenPointBlocks_true j iota hsplit PEL ρ n s labels P H hdual T a v)
      have ht := congrArg Subtype.val
        (l45FullChosenPointBlocks_true j iota hsplit PEL ρ n s labels P H hdual T a' v)
      exact ht.trans ((congrArg (fun z => (z ≫ inc) ≫ bi) hp).trans
        ((Category.assoc (b1 v) inc bi).trans ((hb1 v).trans
          (congrArg (fun z => z ≫ ρ.map r)
            ((Category.assoc (ec a v ≫ snd (H v).group.X (J v).X) inc bi).symm.trans hs.symm)))))
  refine ⟨a', ?_⟩
  exact (l45FullChosenKernelInclusion_point j iota hsplit PEL ρ n s labels P H hdual T a').trans
    ((Finset.prod_congr rfl (fun τ _ => hc τ)).trans
      ((map_prod (IsMonHom.monoidHom (ρ.map r) T) _ _).symm.trans
        (congrArg (fun z => z ≫ ρ.map r)
          (l45FullChosenKernelInclusion_point j iota hsplit PEL ρ n s labels P H hdual T a).symm)))

variable [IsAlgClosed k]

/-- The integral action on the actual full-kernel quotient is descended
from the source; subgroup stability is a theorem above. -/
def l45FullChosenQuotientAction : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E)
    (CMPointsKernels.Construction.l45FullChosenKernelQuotient j iota hsplit PEL ρ n s labels P H hdual).abelian :=
  (CMPointsKernels.Construction.l45FullChosenKernelQuotient j iota hsplit PEL ρ n s labels P H hdual).action ρ
    (l45FullChosenKernel_stable j iota hsplit PEL ρ n s labels P H hdual)

theorem l45FullChosenQuotientAction_intertwines (r : NumberField.RingOfIntegers E) :
    (CMPointsKernels.Construction.l45FullChosenQuotientIsogeny j iota hsplit PEL ρ n s labels P H hdual).hom ≫
        (l45FullChosenQuotientAction j iota hsplit PEL ρ n s labels P H hdual).map r =
      ρ.map r ≫ (CMPointsKernels.Construction.l45FullChosenQuotientIsogeny j iota hsplit PEL ρ n s labels P H hdual).hom :=
  QuotientActionBase.Construction.quotientAction_intertwines ρ
    (CMPointsKernels.Construction.l45FullChosenQuotientIsogeny j iota hsplit PEL ρ n s labels P H hdual)
    ((CMPointsKernels.Construction.l45FullChosenKernelQuotient j iota hsplit PEL ρ n s labels P H hdual).actionStableKernel_of_subgroup
      ρ (l45FullChosenKernel_stable j iota hsplit PEL ρ n s labels P H hdual)) r

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAction.Construction
