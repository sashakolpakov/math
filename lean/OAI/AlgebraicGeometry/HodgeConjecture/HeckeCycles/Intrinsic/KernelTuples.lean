import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryModules

/-! # Kernel Tuples -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelTuples.CM

noncomputable section

/-! The independent rank-three chosen kernels are exactly the tuple of
native projector-supported parameters. The equivalence preserves each
original subgroup on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryModules.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g N s : ℕ} (F : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
  {F0 : Type} [Field F0] [CharZero F0] (base : S ⟶ Spec (.of F0)) (n : ℕ) (labels : Fin s → Gal(E/ℚ))
  (exps : Fin s → Fin 3 → ℕ)
  [∀ v, Module (ZMod (q ^ n)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v))]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

def elementaryTypeEquiv (q : ℕ) (a : Fin 3 → ℕ) :
    Multiplicative (∀ i : Fin 3, ZMod (q ^ a i)) ≃*
      Multiplicative (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q a) :=
  (AddEquiv.ulift : AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q a ≃+ (∀ i : Fin 3, ZMod (q ^ a i))).symm.toMultiplicative

def blockChoice (H : AbelianScheme.TateComparison.Subgroups.KernelChoices F (fun v => j.localCharacter iota (labels v)) n exps) (v : Fin s) :
    KernelChoice.CM.BlockChoice j iota F n (labels v) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v)) :=
  ⟨H.val v, (H.property v).1, (H.property v).2.1, fun k _ _ b =>
    ((H.property v).2.2 k b).map (fun e => e.trans (elementaryTypeEquiv q (exps v)))⟩

def tupleEquiv : AbelianScheme.TateComparison.Subgroups.KernelChoices F (fun v => j.localCharacter iota (labels v)) n exps ≃
    ∀ v : Fin s, AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v))
      (KernelChoice.CM.projector j iota hsplit F n (labels v)) (Over.mk (𝟙 S)) where
  toFun H v := KernelChoice.CM.choiceEquiv j iota hsplit F n (labels v)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v)) base (blockChoice j iota F n labels exps H v)
  invFun H := ⟨fun v => ((KernelChoice.CM.choiceEquiv j iota hsplit F n (labels v)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v)) base).symm (H v)).val,
    fun v => by
      let J := (KernelChoice.CM.choiceEquiv j iota hsplit F n (labels v)
        (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v)) base).symm (H v)
      exact ⟨J.property.1, J.property.2.1, fun k _ _ b =>
        (J.property.2.2 k b).map (fun e => e.trans (elementaryTypeEquiv q (exps v)).symm)⟩⟩
  left_inv H := by
    apply Subtype.ext
    funext v
    exact congrArg Subtype.val ((KernelChoice.CM.choiceEquiv j iota hsplit F n (labels v)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v)) base).symm_apply_apply
        (blockChoice j iota F n labels exps H v))
  right_inv H := by
    funext v
    exact (KernelChoice.CM.choiceEquiv j iota hsplit F n (labels v)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v)) base).apply_symm_apply (H v)

theorem tupleEquiv_membership
    (H : AbelianScheme.TateComparison.Subgroups.KernelChoices F (fun v => j.localCharacter iota (labels v)) n exps)
    (v : Fin s) (T : Over S) (x : T ⟶ F.abelian.scheme) :
    x ∈ (tupleEquiv j iota hsplit F base n labels exps H v).val.subgroup.points T (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase T) ↔
      x ∈ (H.val v).atTest T := Iff.rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelTuples.CM
