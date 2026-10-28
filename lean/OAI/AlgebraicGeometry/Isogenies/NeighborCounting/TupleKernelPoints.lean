import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductPoints

/-! # Tuple Kernel Points -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelPoints

noncomputable section

/-! Recover the actual points of a complete finite kernel product.
Every factor remains a scheme-valued section; no reduction to geometric
points or removal of repeated images occurs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductPoints.Construction

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

theorem tupleKernel_mem_iff (s : ℕ) (F : Fin s → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A) :
    a ∈ (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s F).points T t ↔
      ∃ b : Fin s → (T ⟶ A), (∀ v, b v ∈ (F v).points T t) ∧ ∏ v, b v = a := by
  induction s generalizing a with
  | zero =>
    change a = 1 ↔ _
    simp only [Fin.prod_univ_zero]
    constructor
    · intro ha
      exact ⟨Fin.elim0, fun v => Fin.elim0 v, ha.symm⟩
    · rintro ⟨_, _, ha⟩
      exact ha.symm
  | succ s ih =>
    change (∃ b, b ∈ (F 0).points T t ∧ ∃ c,
      c ∈ (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v => F v.succ)).points T t ∧ a = b * c) ↔ _
    constructor
    · rintro ⟨b, hb, c, hc, ha⟩
      obtain ⟨d, hd, he⟩ := (ih (fun v => F v.succ) c).mp hc
      refine ⟨Fin.cons b d, ?_, ?_⟩
      · intro v
        exact Fin.cases hb hd v
      · simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, he] using ha.symm
    · rintro ⟨b, hb, ha⟩
      refine ⟨b 0, hb 0, ∏ v : Fin s, b v.succ, ?_, ?_⟩
      · exact (ih (fun v => F v.succ) _).mpr ⟨fun v => b v.succ, fun v => hb v.succ, rfl⟩
      · simpa only [Fin.prod_univ_succ] using ha.symm

variable (s : ℕ) (H : Fin s → Grp (Over S)) (i : ∀ v, (H v).X ⟶ A)
variable [∀ v, IsMonHom (i v)]

/-- The original embedding can be compared by its proved coordinate
formula; the representing product itself is kept. -/
theorem fixed_product_family (f : (AbelianScheme.FrobeniusKernel.BlockProducts.Construction.groupBlockProduct s H).X ⟶ A) [IsMonHom f]
    (hf : ∀ (T : Over S) (a : T ⟶ (AbelianScheme.FrobeniusKernel.BlockProducts.Construction.groupBlockProduct s H).X),
      a ≫ f = ∏ v, AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s H T a v ≫ i v) :
    Kernel.Base.fixedKernelFamily (P := P) f = AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v => Kernel.Base.fixedKernelFamily (i v)) := by
  ext T t a
  rw [tupleKernel_mem_iff]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨fun v => AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s H T b v ≫ i v,
      fun v => ⟨AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s H T b v, rfl⟩, (hf T b).symm⟩
  · rintro ⟨b, hb, ha⟩
    choose c hc using hb
    let d := (AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s H T).symm c
    refine ⟨d, ?_⟩
    change d ≫ f = a
    rw [hf]
    have hd : AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s H T d = c :=
      (AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s H T).apply_symm_apply c
    rw [hd]
    exact (Finset.prod_congr rfl (fun v _ => hc v)).trans ha

theorem fixed_paired_product_family (J : Fin s → Grp (Over S))
    (j : ∀ v, (J v).X ⟶ A) [∀ v, IsMonHom (j v)]
    (f : (AbelianScheme.FrobeniusKernel.BlockProducts.Construction.groupBlockProduct s (fun v => H v ⊗ J v)).X ⟶ A) [IsMonHom f]
    (hf : ∀ (T : Over S) (a : T ⟶ (AbelianScheme.FrobeniusKernel.BlockProducts.Construction.groupBlockProduct s (fun v => H v ⊗ J v)).X),
      a ≫ f = ∏ v,
        ((AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (fun v => H v ⊗ J v) T a v ≫ fst _ _) ≫ i v) *
        ((AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (fun v => H v ⊗ J v) T a v ≫ snd _ _) ≫ j v)) :
    Kernel.Base.fixedKernelFamily (P := P) f = AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v =>
      AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (Kernel.Base.fixedKernelFamily (i v)) (Kernel.Base.fixedKernelFamily (j v))) := by
  ext T t a
  rw [tupleKernel_mem_iff]
  constructor
  · rintro ⟨b, rfl⟩
    let c := AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (fun v => H v ⊗ J v) T b
    refine ⟨fun v => ((c v ≫ fst _ _) ≫ i v) * ((c v ≫ snd _ _) ≫ j v), ?_, (hf T b).symm⟩
    intro v
    exact ⟨_, ⟨c v ≫ fst _ _, rfl⟩, _, ⟨c v ≫ snd _ _, rfl⟩, rfl⟩
  · rintro ⟨b, hb, ha⟩
    have hparts : ∀ v, ∃ (l : T ⟶ (H v).X) (r : T ⟶ (J v).X),
        (l ≫ i v) * (r ≫ j v) = b v := by
      intro v
      obtain ⟨x, hx, y, hy, he⟩ := hb v
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := hy
      exact ⟨l, r, he.symm⟩
    choose l r he using hparts
    let c : ∀ v, T ⟶ (H v ⊗ J v).X := fun v => lift (l v) (r v)
    let d := (AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (fun v => H v ⊗ J v) T).symm c
    refine ⟨d, ?_⟩
    change d ≫ f = a
    rw [hf]
    have hd : AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (fun v => H v ⊗ J v) T d = c :=
      (AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (fun v => H v ⊗ J v) T).apply_symm_apply c
    rw [hd]
    simp only [c, lift_fst, lift_snd]
    exact (Finset.prod_congr rfl (fun v _ => he v)).trans ha

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelPoints
