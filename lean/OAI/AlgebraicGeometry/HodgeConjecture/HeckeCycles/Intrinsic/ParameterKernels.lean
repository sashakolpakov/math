import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ParameterBaseChange
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelTuples

/-! # Parameter Kernels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ParameterKernels.CM

noncomputable section

/-! The native tuple parameter at an arbitrary test scheme classifies
the actual chosen kernels of the pulled-back PEL family. Membership is
identified on every further test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g N s : ℕ} (F : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
  {F0 : Type} [Field F0] [CharZero F0] (base : S ⟶ Spec (.of F0)) (P : Over S) (n : ℕ) (labels : Fin s → Gal(E/ℚ))
  (exps : Fin s → Fin 3 → ℕ)
  [∀ v, Module (ZMod (q ^ n)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v))]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

abbrev Parameters := ∀ v : Fin s, AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n)
  (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v)) (KernelChoice.CM.projector j iota hsplit F n (labels v)) P

def kernelEquiv : Parameters j iota hsplit F P n labels exps ≃
    AbelianScheme.TateComparison.Subgroups.KernelChoices (F.pullback P.hom) (fun v => j.localCharacter iota (labels v)) n exps :=
  (Equiv.piCongrRight fun v => ParameterBaseChange.CM.supportedEquiv j iota hsplit F P n
    (labels v) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v))).trans
      (KernelTuples.CM.tupleEquiv j iota hsplit (F.pullback P.hom) (P.hom ≫ base) n labels exps).symm

theorem tuple_kernel (H : Parameters j iota hsplit F P n labels exps) :
    KernelTuples.CM.tupleEquiv j iota hsplit (F.pullback P.hom) (P.hom ≫ base) n labels exps
      (kernelEquiv j iota hsplit F base P n labels exps H) =
    fun v => ParameterBaseChange.CM.supportedEquiv j iota hsplit F P n (labels v)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (exps v)) (H v) :=
  (KernelTuples.CM.tupleEquiv j iota hsplit (F.pullback P.hom) (P.hom ≫ base) n labels exps).apply_symm_apply _

theorem kernelEquiv_membership (H : Parameters j iota hsplit F P n labels exps)
    (v : Fin s) (U : Over P.left) (x : U ⟶ (F.pullback P.hom).abelian.scheme) :
    x ∈ ((kernelEquiv j iota hsplit F base P n labels exps H).val v).atTest U ↔
      (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom (Grp.mk F.abelian.scheme) U).symm x ∈
        (H v).val.subgroup.points ((Over.map P.hom).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U) := by
  have hm := KernelTuples.CM.tupleEquiv_membership j iota hsplit (F.pullback P.hom)
    (P.hom ≫ base) n labels exps (kernelEquiv j iota hsplit F base P n labels exps H) v U x
  have hp := congrArg (fun H' => x ∈ (H' v).val.subgroup.points U (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase U))
    (tuple_kernel j iota hsplit F base P n labels exps H)
  exact hm.symm.trans (iff_of_eq hp)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ParameterKernels.CM
