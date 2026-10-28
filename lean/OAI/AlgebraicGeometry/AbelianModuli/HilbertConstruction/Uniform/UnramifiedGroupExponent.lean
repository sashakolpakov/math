import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleDetection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Unramified Group Exponent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.UnramifiedGroupExponent

noncomputable section

/-! A quasi-compact unramified group whose field-valued points have
finite order is annihilated by one positive integer. Open torsion loci
and a finite subcover retain the full scheme structure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u

theorem quasiCompact_unramifiedGroup_exists_exponent
    {S : Scheme.{u}} (G : Over S) [GrpObj G] [CompactSpace G.left]
    [FormallyUnramified G.hom] [LocallyOfFiniteType G.hom]
    (hfield : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)
      (a : Over.mk s ⟶ G), ∃ n : ℕ, 0 < n ∧ a ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (𝟙 G : G ⟶ G) ^ n = 1 := by
  classical
  have hi (n : ℕ) : IsOpenImmersion (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G n).left :=
    AbelianScheme.IsogenyQuotient.EtaleDetection.Construction.equalizer_openImmersion ((𝟙 G : G ⟶ G) ^ n) (1 : G ⟶ G)
  let U (n : {n : ℕ // 0 < n}) : Set G.left := Set.range (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G n.val).left
  have hU (n : {n : ℕ // 0 < n}) : IsOpen (U n) := by
    let := hi n.val
    exact (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G n.val).left.isOpenEmbedding.isOpen_range
  have hcover : (Set.univ : Set G.left) ⊆ ⋃ n, U n := by
    intro x _
    let k := G.left.residueField x
    let b := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    let s := (b ≫ G.left.fromSpecResidueField x) ≫ G.hom
    let a : Over.mk s ⟶ G := Over.homMk (b ≫ G.left.fromSpecResidueField x) rfl
    obtain ⟨n, hn, ha⟩ := hfield (AlgebraicClosure k) s a
    refine Set.mem_iUnion.mpr ⟨⟨n, hn⟩, ?_⟩
    let x₀ : Spec (.of (AlgebraicClosure k)) := default
    refine ⟨(AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n a ha).left x₀, ?_⟩
    change ((AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n a ha).left ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G n).left) x₀ = x
    rw [← Over.comp_left, AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι]
    exact G.left.fromSpecResidueField_apply x (b x₀)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let N : ℕ := ∏ n ∈ t, n.val
  have hN : 0 < N := Finset.prod_pos (fun n _ => n.property)
  have hsurj : Surjective (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G N).left := by
    constructor
    intro x
    obtain ⟨n, hn, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    obtain ⟨y, hy⟩ := hx
    have hdvd : n.val ∣ N := Finset.dvd_prod_of_mem (fun n => n.val) hn
    have hd : (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G n.val) ^ n.val = 1 :=
      (AbelianScheme.TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n.val (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G n.val)).mp
        ⟨𝟙 _, Category.id_comp _⟩
    have he : (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G n.val) ^ N = 1 := by
      obtain ⟨m, hm⟩ := hdvd
      rw [hm, pow_mul, hd, one_pow]
    refine ⟨(AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift N (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G n.val) he).left y, ?_⟩
    change ((AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift N (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G n.val) he).left ≫
      (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G N).left) y = x
    rw [← Over.comp_left, AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι]
    exact hy
  let : IsIso (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G N).left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hi N, hsurj⟩
  refine ⟨N, hN, ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_epi (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι G N).left).mp
  exact congrArg (fun a : AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme G N ⟶ G => a.left)
    (equalizer.condition ((𝟙 G : G ⟶ G) ^ N) (1 : G ⟶ G))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.UnramifiedGroupExponent
