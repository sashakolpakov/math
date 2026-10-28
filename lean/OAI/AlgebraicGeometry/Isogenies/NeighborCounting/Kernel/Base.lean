import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Tuples
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientGraphs

/-! # Base -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base

noncomputable section

/-!
The complete NeighborCounting kernel, including every compact chosen block and every
opposite annihilator. All subgroups are defined on all test schemes. The
annihilator is the actual pairing annihilator; no ordinary geometric-point
replacement is used. Equality after specialization is proved from equality
of the active subgroup, rather than assumed for the complete kernel.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

instance trivialMap_isMonHom {S : Scheme.{u}} {H M : Over S}
    [GrpObj H] [GrpObj M] : IsMonHom (1 : H ⟶ M) := by
  change IsMonHom (toUnit H ≫ η[M])
  infer_instance

instance graphKernel_isMonHom {S : Scheme.{u}} {A M E H : Over S}
    [GrpObj A] [GrpObj M] [GrpObj E] [GrpObj H]
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) (χ : H ⟶ M)
    [IsMonHom b] [IsMonHom e] [IsMonHom χ] :
    IsMonHom (QuotientGraphs.graphKernel b e χ) := by
  unfold QuotientGraphs.graphKernel
  infer_instance

instance mixedKernel_isMonHom {S : Scheme.{u}} {A M E H : Over S}
    [GrpObj A] [GrpObj M] [GrpObj E] [GrpObj H]
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) [IsMonHom b] [IsMonHom e] :
    IsMonHom (QuotientGraphs.mixedKernel b e) := by
  unfold QuotientGraphs.mixedKernel
  infer_instance

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

/-- The subgroup represented by an actual group map, over a variable test
parameter. Its domain is retained; it is not the set of geometric points. -/
def fixedKernelFamily {H : Over S} [GrpObj H]
    (i : H ⟶ A) [IsMonHom i] : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P where
  points X _ := (IsMonHom.monoidHom i X).range
  naturality := by
    intro X Y f t a ha
    obtain ⟨h, rfl⟩ := ha
    exact ⟨f ≫ h, Category.assoc f h i⟩

omit [IsCommMonObj A] in
theorem fixedKernelFamily_baseChange {H : Over S} [GrpObj H]
    (i : H ⟶ A) [IsMonHom i] {Q : Over S} (b : Q ⟶ P) :
    (fixedKernelFamily (P := P) i).baseChange b = fixedKernelFamily (P := Q) i := rfl

def fixedKernelFamily_model {H : Over S} [GrpObj H]
    (i : H ⟶ A) [IsMonHom i] [Mono i]
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom] :
    (fixedKernelFamily (P := P) i).Model where
  carrier := P ⊗ H
  toBase := fst P H
  toGroup := snd P H ≫ i
  finite := by change IsFinite (pullback.fst P.hom H.hom); infer_instance
  flat := by change Flat (pullback.fst P.hom H.hom); infer_instance
  finitePresentation := by
    change LocallyOfFinitePresentation (pullback.fst P.hom H.hom)
    infer_instance
  jointly_monic X f g hp hi := by
    apply hom_ext
    · exact hp
    · exact (cancel_mono i).mp (by simpa only [Category.assoc] using hi)
  points_iff X t a := by
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨lift t h, lift_fst _ _, by rw [← Category.assoc, lift_snd]; rfl⟩
    · rintro ⟨h, _, ha⟩
      exact ⟨h ≫ snd P H, (Category.assoc _ _ _).trans ha⟩

variable {s : ℕ}
variable (Chosen Opp : Fin s → Over S)
variable [∀ v, GrpObj (Chosen v)] [∀ v, GrpObj (Opp v)]
variable (chosenIn : ∀ v, Chosen v ⟶ A) (oppIn : ∀ v, Opp v ⟶ A)
variable [∀ v, IsMonHom (chosenIn v)] [∀ v, IsMonHom (oppIn v)]
variable {W : Over S} [GrpObj W]
variable (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := Chosen v) (B := Opp v) (W := W))

/-- At multiplier q^n the supplied chosen blocks are their actual q^n
torsion schemes. C0 chooses the whole compact multiplicative block and
zero in the compact etale block. The active subgroup still lies in q-torsion. -/
def chosenKernel (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (v : Fin s) : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P := by
  classical
  exact if v = active then F else
    if multiplicative v then fixedKernelFamily (chosenIn v) else AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup

/-- Opposite kernels are forced by the perfect block pairing at the full
multiplier level, even when the chosen active subgroup is only q-torsion. -/
def forcedOpposite (v : Fin s) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P :=
  AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage (oppIn v)
    ((pairing v).relativeAnnihilator (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (chosenIn v) F))

def fullKernel (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P :=
  AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct
    (chosenKernel Chosen chosenIn active multiplicative F v)
    (forcedOpposite Chosen Opp chosenIn oppIn pairing v
      (chosenKernel Chosen chosenIn active multiplicative F v)))

theorem chosenKernel_baseChange (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) {Q : Over S} (b : Q ⟶ P) (v : Fin s) :
    (chosenKernel Chosen chosenIn active multiplicative F v).baseChange b =
      chosenKernel Chosen chosenIn active multiplicative (F.baseChange b) v := by
  classical
  simp only [chosenKernel]
  split_ifs <;> rfl

omit [IsCommMonObj A] in
theorem forcedOpposite_baseChange (v : Fin s) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    {Q : Over S} (b : Q ⟶ P) :
    (forcedOpposite Chosen Opp chosenIn oppIn pairing v F).baseChange b =
      forcedOpposite Chosen Opp chosenIn oppIn pairing v (F.baseChange b) := by
  rw [forcedOpposite, AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage_baseChange,
    AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.relativeAnnihilator_baseChange, AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback_baseChange]
  rfl

/-- All compact and opposite blocks specialize together with the active
block. This equality is for subgroup functors on every test scheme. -/
theorem fullKernel_baseChange (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) {Q : Over S} (b : Q ⟶ P) :
    (fullKernel Chosen Opp chosenIn oppIn pairing active multiplicative F).baseChange b =
      fullKernel Chosen Opp chosenIn oppIn pairing active multiplicative (F.baseChange b) := by
  unfold fullKernel
  rw [AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel_baseChange]
  congr 1
  funext v
  rw [AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.relativeKernelProduct_baseChange, forcedOpposite_baseChange, chosenKernel_baseChange]

/-- The complete kernel comparison follows from the active comparison;
there is no independently assumed opposite- or compact-block compatibility. -/
theorem fullKernel_specialization_congr (active : Fin s) (multiplicative : Fin s → Bool)
    (F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) {Q : Over S} (b : Q ⟶ P)
    (hactive : F.baseChange b = G.baseChange b) :
    (fullKernel Chosen Opp chosenIn oppIn pairing active multiplicative F).baseChange b =
      (fullKernel Chosen Opp chosenIn oppIn pairing active multiplicative G).baseChange b := by
  rw [fullKernel_baseChange, fullKernel_baseChange, hactive]

omit [GrpObj A] [IsCommMonObj A] in
/-- Equality of pulled-back scheme maps implies equality on every test
scheme mapping to the special base. This uses the actual pullback square. -/
theorem maps_equal_on_special_tests {T : Scheme.{u}} (f : T ⟶ S)
    {H : Over S} (i j : H ⟶ A)
    (h : (Over.pullback f).map i = (Over.pullback f).map j)
    (X : Over S) (t : X ⟶ Over.mk f) (a : X ⟶ H) : a ≫ i = a ≫ j := by
  let liftA : X.left ⟶ pullback H.hom f :=
    pullback.lift a.left t.left (a.w.trans t.w.symm)
  have hfirst : liftA ≫ pullback.fst H.hom f = a.left :=
    pullback.lift_fst _ _ _
  have hh := congrArg
    (fun z => liftA ≫ z.left ≫ pullback.fst A.hom f) h
  apply Over.OverMorphism.ext
  change a.left ≫ i.left = a.left ≫ j.left
  simp only [Over.pullback_map_left, pullback.lift_fst] at hh
  change liftA ≫ (pullback.fst H.hom f ≫ i.left) =
    liftA ≫ (pullback.fst H.hom f ≫ j.left) at hh
  simpa only [← Category.assoc, hfirst] using hh

omit [IsCommMonObj A] in
theorem fixedKernelFamily_specialization_eq {T : Scheme.{u}} (f : T ⟶ S)
    {H : Over S} [GrpObj H] (i j : H ⟶ A) [IsMonHom i] [IsMonHom j]
    (h : (Over.pullback f).map i = (Over.pullback f).map j) :
    (fixedKernelFamily (P := 𝟙_ (Over S)) i).baseChange (toUnit (Over.mk f)) =
      (fixedKernelFamily (P := 𝟙_ (Over S)) j).baseChange (toUnit (Over.mk f)) := by
  ext X t x
  change (∃ a : X ⟶ H, a ≫ i = x) ↔ (∃ a : X ⟶ H, a ≫ j = x)
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (maps_equal_on_special_tests f i j h X t a).symm.trans ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (maps_equal_on_special_tests f i j h X t a).trans ha⟩

/-- A disjoint generic graph and the unique special etale lift have the
same complete kernel after reduction, including every prescribed compact
block and the annihilators in the supplied multiplier-level blocks. -/
theorem full_graph_specialization
    {T : Scheme.{u}} (f : T ⟶ S) (q : ℕ) (hq : q.Prime)
    (hT : (q : Γ(T, ⊤)) = 0)
    [IsIso (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq T hT)]
    {M E H : Over S} [GrpObj M] [GrpObj E] [GrpObj H]
    [Etale ((Over.pullback f).obj H).hom]
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hT ((Over.pullback f).obj M) = 1)
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) (χ : H ⟶ M)
    [IsMonHom b] [IsMonHom e] [IsMonHom χ]
    (active : Fin s) (multiplicative : Fin s → Bool) :
    (fullKernel Chosen Opp chosenIn oppIn pairing active multiplicative
      (fixedKernelFamily (P := 𝟙_ (Over S)) (QuotientGraphs.graphKernel b e χ))).baseChange
        (toUnit (Over.mk f)) =
    (fullKernel Chosen Opp chosenIn oppIn pairing active multiplicative
      (fixedKernelFamily (P := 𝟙_ (Over S)) (QuotientGraphs.graphKernel b e 1))).baseChange
        (toUnit (Over.mk f)) := by
  apply fullKernel_specialization_congr
  exact fixedKernelFamily_specialization_eq f _ _
    (QuotientGraphs.graphKernel_specialization_of_etale f q hq hT hM b e χ)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base
