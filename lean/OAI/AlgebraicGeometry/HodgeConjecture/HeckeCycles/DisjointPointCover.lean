import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct

/-! # Disjoint Point Cover -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DisjointPointCover.CM

noncomputable section

/-! A disjoint open cover classifies actual field-valued points by a
unique component. The inverse point is constructed by the open-immersion
lifting property; no component assignment is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme} {I : Type} {X : Over S} (U : I → Over S) (f : ∀ i, U i ⟶ X)
  [∀ i, IsOpenImmersion (f i).left]
  (hcover : ∀ x : X.left, ∃ i, x ∈ Set.range (f i).left)
  (hdisjoint : Pairwise (fun i j => Disjoint (Set.range (f i).left) (Set.range (f j).left)))
  {k : Type} [Field k] (b : Spec (.of k) ⟶ S)

def assemble (p : Σ i, Over.mk b ⟶ U i) : Over.mk b ⟶ X := p.2 ≫ f p.1

include hcover hdisjoint in
theorem assemble_bijective : Function.Bijective (assemble U f b) := by
  constructor
  · rintro ⟨i, u⟩ ⟨j, v⟩ h
    have hp : (f i).left (u.left (IsLocalRing.closedPoint k)) =
        (f j).left (v.left (IsLocalRing.closedPoint k)) :=
      congrArg (fun z : Over.mk b ⟶ X => z.left (IsLocalRing.closedPoint k)) h
    have hij : i = j := by
      by_contra hne
      exact (Set.disjoint_left.mp (hdisjoint hne)) ⟨_, rfl⟩ ⟨_, hp.symm⟩
    subst j
    have : Mono (f i) := Over.mono_of_mono_left (f i)
    have huv : u = v := (cancel_mono (f i)).mp h
    cases huv
    rfl
  · intro p
    obtain ⟨i, hi⟩ := hcover (p.left (IsLocalRing.closedPoint k))
    have hrange : Set.range p.left ⊆ Set.range (f i).left := by
      rintro x ⟨t, rfl⟩
      have ht := @Subsingleton.elim (Spec (.of k)) inferInstance t (IsLocalRing.closedPoint k)
      simpa only [ht] using hi
    let u := IsOpenImmersion.lift (f i).left p.left hrange
    have hu : u ≫ (f i).left = p.left := IsOpenImmersion.lift_fac _ _ _
    have hb : u ≫ (U i).hom = b :=
      (congrArg (u ≫ ·) (f i).w.symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.hom) hu).trans p.w))
    exact ⟨⟨i, Over.homMk u hb⟩, Over.OverMorphism.ext hu⟩

def pointEquiv : (Σ i, Over.mk b ⟶ U i) ≃ (Over.mk b ⟶ X) :=
  Equiv.ofBijective (assemble U f b) (assemble_bijective U f hcover hdisjoint b)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DisjointPointCover.CM
