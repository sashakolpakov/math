import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff
import Mathlib.RingTheory.DualNumber

/-! # Etale Tangents -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.EtaleTangents.CM

/-! Constant etale group schemes have no nonidentity dual-number
tangent points; the proof retains the nilpotent test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (k : Type) [Field k]

theorem dualNumber_subsingleton : Subsingleton (Spec (.of (DualNumber k))) := by
  refine ⟨fun x y => ?_⟩
  have hid (p : PrimeSpectrum (DualNumber k)) :
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber k) := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal p.isPrime.ne_top
    · rw [DualNumber.maximalIdeal_eq_span_singleton_eps]
      apply Ideal.span_le.mpr
      intro z hz
      have hz' : z = (DualNumber.eps : DualNumber k) := Set.mem_singleton_iff.mp hz
      rw [hz']
      exact p.isPrime.mem_of_pow_mem 2 (by simp)
  exact PrimeSpectrum.ext (by rw [hid x, hid y])

theorem constant_hom_ext (I : Type)
    (f g : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I)
    (h : AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ f = AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ g) : f = g := by
  let : Subsingleton (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k).left := dualNumber_subsingleton k
  apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of k)) I (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k)).injective
  apply LocallyConstant.ext
  intro t
  have he := congrArg (fun z : Over.mk (𝟙 (Spec (.of k))) ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I =>
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (Over.mk (𝟙 (Spec (.of k)))) z (IsLocalRing.closedPoint k)) h
  change AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k) f
      ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k).left (IsLocalRing.closedPoint k)) =
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k) g
      ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k).left (IsLocalRing.closedPoint k)) at he
  exact (congrArg (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k) f) (Subsingleton.elim _ _)).trans
    (he.trans (congrArg (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k) g) (Subsingleton.elim _ _)))

theorem point_eq_one (I : Type) [Group I]
    (p : TangentRank.CM.Points (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) I)) : p.val = 1 :=
  constant_hom_ext k I p.val
    (1 : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) I).X)
    (p.property.trans (MonObj.comp_one _).symm)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.EtaleTangents.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.EtaleTangents.CM.SplitTangentRank

/-! Adding the actual constant etale factor leaves tangent rank
unchanged, so an ordinary splitting determines the original tangent rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank.CM

variable {k : Type} [Field k]

def pointMap {G H : Grp (Over (Spec (.of k)))} (f : G ⟶ H) : TangentRank.CM.Points G → TangentRank.CM.Points H :=
  fun p => ⟨p.val ≫ f.hom.hom, by rw [← Category.assoc, p.property, MonObj.one_comp]⟩

theorem rank_of_bijective {G H : Grp (Over (Spec (.of k)))} (f : G ⟶ H)
    (hf : Function.Bijective (pointMap f)) {d : ℕ} (hd : TangentRank.CM.HasRank G d) : TangentRank.CM.HasRank H d := by
  obtain ⟨c, ha, hs⟩ := hd
  refine ⟨c.trans (Equiv.ofBijective (pointMap f) hf), ?_, ?_⟩
  · intro x y
    change (c (x + y)).val ≫ f.hom.hom = _
    rw [ha, MonObj.mul_comp]
    rfl
  · intro a x
    change (c (a • x)).val ≫ f.hom.hom = _
    rw [hs, Category.assoc]
    rfl

def inclusion (G : Grp (Over (Spec (.of k)))) (I : Type) [Group I] :
    G ⟶ Grp.mk (G.X ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) I).X) := by
  let E := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) I
  let : IsMonHom (1 : G.X ⟶ E.X) :=
    inferInstanceAs (IsMonHom (toUnit G.X ≫ η[E.X]))
  exact Grp.ofHom (lift (𝟙 G.X) (1 : G.X ⟶ E.X))

theorem inclusion_bijective (G : Grp (Over (Spec (.of k)))) (I : Type) [Group I] :
    Function.Bijective (pointMap (inclusion G I)) := by
  let E := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) I
  constructor
  · intro p t he
    apply Subtype.ext
    have h := congrArg (fun z : TangentRank.CM.Points (Grp.mk (G.X ⊗ E.X)) => z.val ≫ fst G.X E.X) he
    change (p.val ≫ lift (𝟙 G.X) (1 : G.X ⟶ E.X)) ≫ fst G.X E.X =
      (t.val ≫ lift (𝟙 G.X) (1 : G.X ⟶ E.X)) ≫ fst G.X E.X at h
    simpa only [Category.assoc, lift_fst, Category.comp_id] using h
  · intro p
    let t : TangentRank.CM.Points G := ⟨p.val ≫ fst G.X E.X, by
      rw [← Category.assoc, p.property, MonObj.one_comp]⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply hom_ext
    · change ((p.val ≫ fst G.X E.X) ≫ lift (𝟙 G.X) (1 : G.X ⟶ E.X)) ≫ fst G.X E.X = _
      simp only [Category.assoc, lift_fst, Category.comp_id]
      rfl
    · change ((p.val ≫ fst G.X E.X) ≫ lift (𝟙 G.X) (1 : G.X ⟶ E.X)) ≫ snd G.X E.X = _
      rw [Category.assoc, lift_snd, MonObj.comp_one]
      exact (point_eq_one k I
        ⟨p.val ≫ snd G.X E.X, by rw [← Category.assoc, p.property, MonObj.one_comp]⟩).symm

theorem ordinary_rank {B : Grp (Over (Spec (.of k)))} (q n d r : ℕ)
    [Fact q.Prime] [CharP k q]
    (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k B q (n + 1) d r) : TangentRank.CM.HasRank B d := by
  have ht := rank_of_bijective
    (inclusion (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q (n + 1) d)
      (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) r))
    (inclusion_bijective _ _) (TangentRank.CM.multiplicative_rank q n d)
  exact TangentRank.CM.rank_transport e.symm ht

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.EtaleTangents.CM.SplitTangentRank

end

end OAI
