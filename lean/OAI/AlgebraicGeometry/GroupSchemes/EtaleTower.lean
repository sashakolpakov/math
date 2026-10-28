import OAI.AlgebraicGeometry.GroupSchemes.ConnectedTower

/-! # Etale Tower -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! Uniqueness of affine lifts propagates from the first level to the entire tower. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k]

/-- Triviality of a point-map kernel propagates through every level of the tower. -/
theorem FiniteEtale.PDivisibleGroup.pointMap_kernel_of_first {p h : ℕ} (G : FiniteEtale.PDivisibleGroup k p h)
    {R S : CommAlgCat.{u} k} (a : R ⟶ S)
    (hfirst : ∀ x : FiniteEtale.affine k R ⟶ (G.level 1).scheme,
      (algSpec (CommRingCat.of k)).map a.op ≫ x = 1 → x = 1) :
    ∀ n, ∀ x : FiniteEtale.affine k R ⟶ (G.level n).scheme,
      (algSpec (CommRingCat.of k)).map a.op ≫ x = 1 → x = 1 := by
  intro n
  cases n with
  | zero =>
    intro x _
    simpa only [pow_zero, pow_one] using G.annihilated k 0 R x
  | succ n =>
    induction n with
    | zero => exact hfirst
    | succ n ih =>
      intro x hxmap
      have hkernel : ∀ z : FiniteEtale.affine k R ⟶ (G.level (n + 1 + 1)).scheme,
          z ^ (p ^ (n + 1)) = 1 →
          (algSpec (CommRingCat.of k)).map a.op ≫ z = 1 → z = 1 := by
        intro z hz hzmap
        obtain ⟨y, hy⟩ := (G.kernel (n + 1) R z).mpr hz
        have hymap : (algSpec (CommRingCat.of k)).map a.op ≫ y = 1 := by
          apply (cancel_mono (G.inclusion (n + 1))).mp
          rw [Category.assoc, hy, hzmap, MonObj.one_comp]
        rw [← hy, ih y hymap, MonObj.one_comp]
      have hxp : x ^ p = 1 := by
        apply hkernel
        · rw [← pow_mul, ← pow_succ']
          exact G.annihilated k (n + 1 + 1) R x
        · rw [MonObj.comp_pow, hxmap, one_pow]
      apply hkernel
      · rw [pow_succ', pow_mul, hxp, one_pow]
      · exact hxmap

/-- Injectivity of a map on first-level points implies injectivity at every level. -/
theorem FiniteEtale.PDivisibleGroup.pointMap_injective_of_first {p h : ℕ} (G : FiniteEtale.PDivisibleGroup k p h)
    {R S : CommAlgCat.{u} k} (a : R ⟶ S)
    (hfirst : Function.Injective ((G.level 1).points.map a)) (n : ℕ) :
    Function.Injective ((G.level n).points.map a) := by
  apply (injective_iff_map_eq_one ((G.level n).points.map a).hom).mpr
  apply G.pointMap_kernel_of_first a
  exact (injective_iff_map_eq_one ((G.level 1).points.map a).hom).mp hfirst

/-- Formal unramifiedness of the first level propagates through the tower. -/
theorem FiniteEtale.PDivisibleGroup.formallyUnramified_of_first {p h : ℕ} (G : FiniteEtale.PDivisibleGroup k p h)
    (hfirst : Algebra.FormallyUnramified k (G.level 1).algebra) (n : ℕ) :
    Algebra.FormallyUnramified k (G.level n).algebra := by
  have := hfirst
  apply Algebra.FormallyUnramified.iff_comp_injective.mpr
  intro B _ _ I hI
  let a : CommAlgCat.of k B ⟶ CommAlgCat.of k (B ⧸ I) :=
    CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)
  have hi : Function.Injective ((G.level 1).points.map a) :=
    ((G.level 1).pointMap_injective_iff a).mpr
      (Algebra.FormallyUnramified.comp_injective I hI)
  exact ((G.level n).pointMap_injective_iff a).mp (G.pointMap_injective_of_first a hi n)

/-- Over an algebraically closed field, a split étale first level makes every level split étale. -/
theorem FiniteEtale.PDivisibleGroup.split_of_first_split [IsAlgClosed k] {p h : ℕ} (G : FiniteEtale.PDivisibleGroup k p h)
    (hfirst : Algebra.IsFiniteSplit k (G.level 1).algebra) (n : ℕ) :
    Algebra.IsFiniteSplit k (G.level n).algebra := by
  have := hfirst
  have := G.formallyUnramified_of_first inferInstance n
  have : Algebra.FormallyEtale k (G.level n).algebra :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field k (G.level n).algebra
  infer_instance

end

end OAI.AlgebraicGeometry.GroupSchemes
