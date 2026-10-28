import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePointSubgroups
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricBlockSubgroups
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientFibers

/-! # Geometric Kernel Choices -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianScheme.TateComparison

/-! The exact finite-etale, eigenblock, and geometric-type conditions of
TateComparison are equivalent to IsogenyQuotient's supported relative subgroup choices. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  {S : Scheme}
  (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) (n : ℕ)
  (M : Type) [AddCommGroup M] [Module (ZMod (q ^ n)) M] [Finite M]

/-- One chosen subgroup with precisely the original three conditions,
allowing a general finite elementary group as the type parameter. -/
def Data.SphericalPELAlbaneseData.TypedBlockChoice (v : Fin s × Bool) :=
  {J : Subgroups.PointSubgroup F.abelian // J.HasFiniteEtaleModel ∧
    (∀ T, J.atTest T ≤ (Subgroups.splitBlock F (D.localCharacter v) n).atTest T) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S),
      Nonempty (J.atTest (Over.mk b) ≃* Multiplicative M)}

def Data.SphericalPELAlbaneseData.typedBlockToSupported (v : Fin s × Bool) (J : D.TypedBlockChoice F n M v) :
    IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      (D.integralProjectorMap hg F n v) (Over.mk (𝟙 S)) := by
  refine ⟨{
    subgroup := RelativePointSubgroups.pointToRelativeSubgroup F.abelian J.val
    killed := ?_
    moduleType := ?_
    geometric := RelativePointSubgroups.pointToRelative_hasModel F.abelian J.val J.property.1 }, ?_⟩
  · intro T t x hx
    exact (J.property.2.1 T hx).1
  · intro k _ _ b t
    exact J.property.2.2 k b
  · intro T t x hx
    exact ((D.splitBlock_mem_iff_integral_fixed hg F n T v x).mp (J.property.2.1 T hx)).2

variable (base : S ⟶ Spec (.of K))

def Data.SphericalPELAlbaneseData.supportedToTypedBlock (v : Fin s × Bool)
    (H : IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      (D.integralProjectorMap hg F n v) (Over.mk (𝟙 S))) :
    D.TypedBlockChoice F n M v := by
  refine ⟨RelativePointSubgroups.relativeToPointSubgroup F.abelian H.val.subgroup, ?_, ?_, ?_⟩
  · obtain ⟨R⟩ := H.val.geometric
    exact RelativePointSubgroups.relativeToPoint_hasFiniteEtaleModel F.abelian H.val.subgroup R (q ^ n) H.val.killed
      (TorsionQuotient.Etale.TorsionEtale.torsion_etale F.abelian.scheme (q ^ n)
        (IsogenyQuotient.Unit.Construction.positive_integer_unit_on_characteristic_zero_base base (q ^ n)
          (pow_pos (Fact.out : q.Prime).pos n)))
  · intro T x hx
    exact (D.splitBlock_mem_iff_integral_fixed hg F n T v x).mpr
      ⟨H.val.killed T (RelativePointSubgroups.testToBase T) x hx, H.property T (RelativePointSubgroups.testToBase T) x hx⟩
  · intro k _ _ b
    exact H.val.moduleType k b (RelativePointSubgroups.testToBase (Over.mk b))

def Data.SphericalPELAlbaneseData.typedBlockSupportedEquiv (v : Fin s × Bool) :
    D.TypedBlockChoice F n M v ≃
      IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
        (D.integralProjectorMap hg F n v) (Over.mk (𝟙 S)) where
  toFun := D.typedBlockToSupported hg F n M v
  invFun := D.supportedToTypedBlock hg F n M base v
  left_inv J := by
    apply Subtype.ext
    exact RelativePointSubgroups.relativeToPoint_pointToRelative F.abelian J.val
  right_inv H := by
    apply Subtype.ext
    apply TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext
    exact RelativePointSubgroups.pointToRelative_relativeToPoint F.abelian H.val.subgroup

variable {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K))
  (G : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k)))

def Data.SphericalPELAlbaneseData.geometricTypedBlockEquiv (v : Fin s × Bool) :
    D.TypedBlockChoice G n M v ≃
      {J : AddSubgroup (D.torsionBlock hg (Over.mk (𝟙 (Spec (.of k)))) G n v) // Nonempty (J ≃+ M)} :=
  (D.typedBlockSupportedEquiv hg G n M b v).trans
    (D.geometricSplitBlockChoices hg G n b k (𝟙 (Spec (.of k))) M v)

theorem Data.SphericalPELAlbaneseData.geometricTypedBlockEquiv_membership (v : Fin s × Bool)
    (J : D.TypedBlockChoice G n M v)
    (x : D.torsionBlock hg (Over.mk (𝟙 (Spec (.of k)))) G n v) :
    x ∈ (D.geometricTypedBlockEquiv hg n M b G v J).val ↔
      x.val.val.toMul ∈ J.val.atTest (Over.mk (𝟙 (Spec (.of k)))) :=
  D.geometricSplitBlockChoices_membership hg G n b k (𝟙 (Spec (.of k))) M v
    (D.typedBlockToSupported hg G n M v J) x

end AlgebraicGeometry.AbelianScheme.TateComparison

namespace AlgebraicGeometry.AbelianScheme.TateComparison.GeometricKernelChoices

/-! The original independent IsogenyQuotient kernel choices, and hence actual
correspondence fibers, classify independent typed subgroups of the
actual finite Tate blocks over every algebraically closed field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- The elementary group of a bounded type is killed by the common
multiplier, giving its canonical finite-level scalar action. -/
abbrev elementaryTorsionModule (q h : ℕ) (a : Fin 3 → ℕ) (ha : ∀ i, a i ≤ h) :
    Module (ZMod (q ^ h)) (∀ i : Fin 3, ZMod (q ^ a i)) :=
  AddCommGroup.zmodModule (fun x => by
    funext i
    change q ^ h • x i = 0
    rw [nsmul_eq_mul, (ZMod.natCast_eq_zero_iff (q ^ h) (q ^ a i)).mpr (pow_dvd_pow q (ha i)), zero_mul])

namespace SphericalPELAlbaneseData

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {S : Scheme} (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S)
  (t : Local.IntegralType s)

local instance (n : ℕ) : NeZero (q ^ n) := ⟨pow_ne_zero n (Fact.out : q.Prime).ne_zero⟩

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.kernelChoicesTypedBlockEquiv :
    Subgroups.KernelChoices F (fun v => D.localCharacter (v, false)) t.multiplierNat t.exponentNat ≃
      ∀ v : Fin s, D.TypedBlockChoice F t.multiplierNat
        (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)) (v, false) where
  toFun H v := ⟨H.val v, H.property v⟩
  invFun H := ⟨fun v => (H v).val, fun v => (H v).property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext fun _ => Subtype.ext rfl

variable (hg : D.IsGoodCompletelySplitPrime)
  {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K))
  (G : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k)))

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricKernelChoicesEquiv :
    Subgroups.KernelChoices G (fun v => D.localCharacter (v, false)) t.multiplierNat t.exponentNat ≃
      ∀ v : Fin s,
        {J : AddSubgroup (D.torsionBlock hg (Over.mk (𝟙 (Spec (.of k)))) G t.multiplierNat (v, false)) //
          Nonempty (J ≃+ (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)))} :=
  (D.kernelChoicesTypedBlockEquiv G t).trans (Equiv.piCongrRight fun v => by
    letI := elementaryTorsionModule q t.multiplierNat (t.exponentNat v) (t.exponentNat_le v)
    exact D.geometricTypedBlockEquiv hg t.multiplierNat
      (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)) b G (v, false))

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricKernelChoicesEquiv_membership
    (H : Subgroups.KernelChoices G (fun v => D.localCharacter (v, false)) t.multiplierNat t.exponentNat)
    (v : Fin s)
    (x : D.torsionBlock hg (Over.mk (𝟙 (Spec (.of k)))) G t.multiplierNat (v, false)) :
    x ∈ (D.geometricKernelChoicesEquiv t hg b G H v).val ↔
      x.val.val.toMul ∈ (H.val v).atTest (Over.mk (𝟙 (Spec (.of k)))) := by
  let := elementaryTorsionModule q t.multiplierNat (t.exponentNat v) (t.exponentNat_le v)
  exact D.geometricTypedBlockEquiv_membership hg t.multiplierNat
    (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)) b G (v, false) ⟨H.val v, H.property v⟩ x

variable (hIsogenyQuotient : D.RealizesIsogenyQuotient) (x : D.GeometricPoint b)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46FiberTorsionSubgroupEquiv :
    (D.correspondence t).Fiber x ≃
      ∀ v : Fin s,
        {J : AddSubgroup (D.torsionBlock hg (Over.mk (𝟙 (Spec (.of k))))
            (D.fiberFamily b x) t.multiplierNat (v, false)) //
          Nonempty (J ≃+ (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)))} :=
  (D.c46FiberKernelEquiv hIsogenyQuotient t x).trans
    (D.geometricKernelChoicesEquiv t hg b (D.fiberFamily b x))

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46FiberTorsionSubgroupEquiv_membership (c : (D.correspondence t).Fiber x) (v : Fin s)
    (z : D.torsionBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) t.multiplierNat (v, false)) :
    z ∈ (D.c46FiberTorsionSubgroupEquiv t hg b hIsogenyQuotient x c v).val ↔
      z.val.val.toMul ≫
        (D.c46FiberIsogeny hIsogenyQuotient t x (c.val ≫ (D.correspondence t).target)
          c.val c.property rfl).isogeny.hom = 1 := by
  have hm := D.geometricKernelChoicesEquiv_membership t hg b (D.fiberFamily b x)
    (D.c46FiberKernelEquiv hIsogenyQuotient t x c) v z
  change z ∈ (D.c46FiberTorsionSubgroupEquiv t hg b hIsogenyQuotient x c v).val ↔ _ at hm
  rw [hm]
  change z.val.val.toMul ∈
    (D.chosenKernelAtLift t (D.c46Isogeny hIsogenyQuotient t) x c.val c.property v).atTest _ ↔ _
  rw [← D.c46FiberIsogeny_kernel hIsogenyQuotient t x (c.val ≫ (D.correspondence t).target)
    c.val c.property rfl v]
  change (_ = 1 ∧ z.val.val.toMul ∈
    (Subgroups.splitBlock (D.fiberFamily b x) (D.localCharacter (v, false)) t.multiplierNat).atTest _) ↔ _
  exact and_iff_left ((D.torsionBlock_mem_iff hg _ (D.fiberFamily b x) t.multiplierNat (v, false) z.val).mp z.property)

end SphericalPELAlbaneseData

end AlgebraicGeometry.AbelianScheme.TateComparison.GeometricKernelChoices

end

end OAI
