import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePointSubgroups
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale

/-! # Kernel Choice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM

noncomputable section

/-! Identify TateComparison's actual chosen point-subgroup with IsogenyQuotient's supported
relative subgroup for the same CMPoints projector. This works on every test
scheme, retaining the original subgroup and its finite geometric type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g N : ℕ} (F : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
  (n : ℕ) (τ : Gal(E/ℚ)) (M : Type) [AddCommGroup M] [Module (ZMod (q ^ n)) M] [Finite M]

def BlockChoice :=
  {J : AbelianScheme.TateComparison.Subgroups.PointSubgroup F.abelian // J.HasFiniteEtaleModel ∧
    (∀ T, J.atTest T ≤ (AbelianScheme.TateComparison.Subgroups.splitBlock F (j.localCharacter iota τ) n).atTest T) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S),
      Nonempty (J.atTest (Over.mk b) ≃* Multiplicative M)}

abbrev projector := (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ)

def toSupported (J : BlockChoice j iota F n τ M) :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M (CM.projector j iota hsplit F n τ) (Over.mk (𝟙 S)) := by
  refine ⟨{
    subgroup := AbelianScheme.TateComparison.RelativePointSubgroups.pointToRelativeSubgroup F.abelian J.val
    killed := ?_
    moduleType := ?_
    geometric := AbelianScheme.TateComparison.RelativePointSubgroups.pointToRelative_hasModel F.abelian J.val J.property.1 }, ?_⟩
  · intro T t x hx
    exact (J.property.2.1 T hx).1
  · intro k _ _ b t
    exact J.property.2.2 k b
  · intro T t x hx
    exact ((PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) n τ T x).mp
      (J.property.2.1 T hx)).2

variable {F0 : Type} [Field F0] [CharZero F0] (base : S ⟶ Spec (.of F0))

def ofSupported
    (H : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M (CM.projector j iota hsplit F n τ) (Over.mk (𝟙 S))) :
    BlockChoice j iota F n τ M := by
  refine ⟨AbelianScheme.TateComparison.RelativePointSubgroups.relativeToPointSubgroup F.abelian H.val.subgroup, ?_, ?_, ?_⟩
  · obtain ⟨R⟩ := H.val.geometric
    exact AbelianScheme.TateComparison.RelativePointSubgroups.relativeToPoint_hasFiniteEtaleModel F.abelian H.val.subgroup R (q ^ n) H.val.killed
      (AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_etale F.abelian.scheme (q ^ n)
        (AbelianScheme.IsogenyQuotient.Unit.Construction.positive_integer_unit_on_characteristic_zero_base base (q ^ n)
          (pow_pos (Fact.out : q.Prime).pos n)))
  · intro T x hx
    exact (PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) n τ T x).mpr
      ⟨H.val.killed T (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase T) x hx, H.property T (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase T) x hx⟩
  · intro k _ _ b
    exact H.val.moduleType k b (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (Over.mk b))

def choiceEquiv : BlockChoice j iota F n τ M ≃
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M (CM.projector j iota hsplit F n τ) (Over.mk (𝟙 S)) where
  toFun := toSupported j iota hsplit F n τ M
  invFun := ofSupported j iota hsplit F n τ M base
  left_inv J := Subtype.ext (AbelianScheme.TateComparison.RelativePointSubgroups.relativeToPoint_pointToRelative F.abelian J.val)
  right_inv H := by
    apply Subtype.ext
    apply AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext
    exact AbelianScheme.TateComparison.RelativePointSubgroups.pointToRelative_relativeToPoint F.abelian H.val.subgroup

theorem choiceEquiv_membership (J : BlockChoice j iota F n τ M) (T : Over S)
    (x : T ⟶ F.abelian.scheme) :
    x ∈ (choiceEquiv j iota hsplit F n τ M base J).val.subgroup.points T (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase T) ↔
      x ∈ J.val.atTest T := Iff.rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM
