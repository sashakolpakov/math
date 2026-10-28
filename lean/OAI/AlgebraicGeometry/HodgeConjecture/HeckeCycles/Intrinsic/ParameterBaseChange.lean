import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterChoiceEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice

/-! # Parameter Base Change -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ParameterBaseChange.CM

noncomputable section

/-! Native CMPoints projector-supported parameters over a test scheme are
the same parameters of the actual pulled-back PEL family. The projector
identity follows from base change of the original integral action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM

def supportCongr {S : Scheme} (A : Over S) [GrpObj A]
    (n : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (p p' : A ⟶ A) (h : p = p') (T : Over S) :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A n M p T ≃ AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A n M p' T where
  toFun F := ⟨F.val, h ▸ F.property⟩
  invFun F := ⟨F.val, h.symm ▸ F.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g N : ℕ} (F : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
  (P : Over S) (n : ℕ) (τ : Gal(E/ℚ))

theorem projector_pullback :
    KernelChoice.CM.projector j iota hsplit (F.pullback P.hom) n τ =
      (Over.pullback P.hom).map (KernelChoice.CM.projector j iota hsplit F n τ) :=
  F.pullback_action_schemeMap P.hom (j.projector iota hsplit n τ)

variable (M : Type) [AddCommGroup M] [Module (ZMod (q ^ n)) M] [Finite M]

def supportedEquiv :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M (KernelChoice.CM.projector j iota hsplit F n τ) P ≃
      AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice (F.pullback P.hom).abelian.scheme (q ^ n) M
        (KernelChoice.CM.projector j iota hsplit (F.pullback P.hom) n τ) (Over.mk (𝟙 P.left)) :=
  (ParameterChoiceEquiv.CM.supportedEquiv (Grp.mk F.abelian.scheme) P (q ^ n) M
    (KernelChoice.CM.projector j iota hsplit F n τ)).trans
      (supportCongr (F.pullback P.hom).abelian.scheme (q ^ n) M _ _
        (projector_pullback j iota hsplit F P n τ).symm (Over.mk (𝟙 P.left)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ParameterBaseChange.CM
