import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Coherent Lifting -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CoherentLifting.Cycles

noncomputable section

/-!
# Coherent cycles in countable inverse towers of chain complexes

Surjective transition maps in each degree allow boundary corrections to be
lifted. Recursively correcting representatives therefore realizes a coherent
family of native homology classes by a coherent family of native cycles.
The same construction in the next degree gives uniqueness when the next
homology groups vanish.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

universe u v

variable {R : Type u} [Ring R]
variable {K L : ChainComplex (ModuleCat.{v} R) ℕ}

/-- A zero native homology class has an actual incoming boundary preimage,
also in degree zero of a nonnegative chain complex. -/
theorem exists_toCycles_eq_of_homologyπ_eq_zero
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (z : K.cycles n) (hz : K.homologyπ n z = 0) :
    ∃ b : K.X (n + 1), K.toCycles (n + 1) n b = z := by
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
      (K.toCycles_comp_homologyπ (n + 1) n)
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (K.homologyIsCokernel (n + 1) n
      ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)))
  exact (ShortComplex.moduleCat_exact_iff S).mp hS z hz

/-- Boundary maps into native cycle objects commute with chain maps. -/
theorem chainToCycles_naturality (f : K ⟶ L) (n : ℕ) :
    K.toCycles (n + 1) n ≫ cyclesMap f n = f.f (n + 1) ≫ L.toCycles (n + 1) n := by
  apply (cancel_mono (L.iCycles n)).mp
  rw [Category.assoc, cyclesMap_i, ← Category.assoc, toCycles_i,
    Category.assoc, toCycles_i]
  exact (f.comm (n + 1) n).symm

/-- Elementwise form of boundary naturality. -/
theorem chainToCycles_naturality_apply (f : K ⟶ L) (n : ℕ) (b : K.X (n + 1)) :
    cyclesMap f n (K.toCycles (n + 1) n b) = L.toCycles (n + 1) n (f.f (n + 1) b) :=
  ConcreteCategory.congr_hom (chainToCycles_naturality f n) b

/-- Elementwise naturality of the native homology projection. -/
theorem chainHomologyπ_naturality_apply (f : K ⟶ L) (n : ℕ) (z : K.cycles n) :
    L.homologyπ n (cyclesMap f n z) = homologyMap f n (K.homologyπ n z) :=
  (ConcreteCategory.congr_hom (homologyπ_naturality f n) z).symm

/-- Given a prescribed lower-level cycle and an upper-level homology class
mapping to it, lift a boundary correction to make the representatives agree. -/
theorem exists_cycle_representative_lifting (f : K ⟶ L) (n : ℕ)
    (hsurj : Function.Surjective (f.f (n + 1)))
    (c : K.homology n) (z : L.cycles n)
    (hc : homologyMap f n c = L.homologyπ n z) :
    ∃ w : K.cycles n, K.homologyπ n w = c ∧ cyclesMap f n w = z := by
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance c
  have hz : L.homologyπ n (z - cyclesMap f n w) = 0 := by
    rw [map_sub, chainHomologyπ_naturality_apply, hw, hc, sub_self]
  obtain ⟨b, hb⟩ := exists_toCycles_eq_of_homologyπ_eq_zero L n _ hz
  obtain ⟨a, ha⟩ := hsurj b
  refine ⟨w + K.toCycles (n + 1) n a, ?_, ?_⟩
  · rw [map_add, hw]
    have hzero := ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ (n + 1) n) a
    change K.homologyπ n (K.toCycles (n + 1) n a) = 0 at hzero
    rw [hzero, add_zero]
  · rw [map_add, chainToCycles_naturality_apply, ha, hb]
    abel

/-- Coherent native homology classes admit coherent native cycle
representatives. Only surjectivity in the incoming boundary degree is needed. -/
theorem exists_coherent_cycle_representatives
    (C : ℕ → ChainComplex (ModuleCat.{v} R) ℕ) (p : ∀ i, C (i + 1) ⟶ C i)
    (n : ℕ) (hsurj : ∀ i, Function.Surjective ((p i).f (n + 1)))
    (c : ∀ i, (C i).homology n)
    (hc : ∀ i, homologyMap (p i) n (c (i + 1)) = c i) :
    ∃ z : ∀ i, (C i).cycles n,
      (∀ i, (C i).homologyπ n (z i) = c i) ∧
      ∀ i, cyclesMap (p i) n (z (i + 1)) = z i := by
  classical
  let V (i : ℕ) := {z : (C i).cycles n // (C i).homologyπ n z = c i}
  have step : ∀ i, ∀ z : V i, ∃ w : V (i + 1), cyclesMap (p i) n w.val = z.val := by
    intro i z
    obtain ⟨w, hw, hmap⟩ := exists_cycle_representative_lifting (p i) n (hsurj i)
      (c (i + 1)) z.val ((hc i).trans z.property.symm)
    exact ⟨⟨w, hw⟩, hmap⟩
  choose next hnext using step
  obtain ⟨z₀, hz₀⟩ := (ModuleCat.epi_iff_surjective ((C 0).homologyπ n)).mp inferInstance (c 0)
  let z : ∀ i, V i := Nat.rec ⟨z₀, hz₀⟩ next
  exact ⟨fun i => (z i).val, fun i => (z i).property, fun i => hnext i (z i)⟩

/-- Vanishing of the next homology group makes it possible to lift a
prescribed primitive, correcting its discrepancy by a higher boundary. -/
theorem exists_boundary_primitive_lifting (f : K ⟶ L) (n : ℕ)
    (hsurj : Function.Surjective (f.f (n + 2)))
    (hvanish : IsZero (L.homology (n + 1)))
    (z : K.cycles n) (hz : K.homologyπ n z = 0)
    (b : L.X (n + 1)) (hb : L.toCycles (n + 1) n b = cyclesMap f n z) :
    ∃ a : K.X (n + 1), K.toCycles (n + 1) n a = z ∧ f.f (n + 1) a = b := by
  obtain ⟨a₀, ha₀⟩ := exists_toCycles_eq_of_homologyπ_eq_zero K n z hz
  let δ := b - f.f (n + 1) a₀
  have hδ : L.toCycles (n + 1) n δ = 0 := by
    dsimp only [δ]
    rw [map_sub, hb, ← chainToCycles_naturality_apply, ha₀, sub_self]
  have hδd : L.d (n + 1) n δ = 0 := by
    have h := congrArg (L.iCycles n) hδ
    rw [map_zero] at h
    exact (ConcreteCategory.congr_hom (L.toCycles_i (n + 1) n) δ).symm.trans h
  have hExact : L.ExactAt (n + 1) := (exactAt_iff_isZero_homology L (n + 1)).mpr hvanish
  have hsc : (L.sc' (n + 2) (n + 1) n).Exact :=
    (L.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).mp hExact
  obtain ⟨e, he⟩ : ∃ e : L.X (n + 2), L.d (n + 2) (n + 1) e = δ :=
    (ShortComplex.moduleCat_exact_iff _).mp hsc δ hδd
  obtain ⟨e', he'⟩ := hsurj e
  refine ⟨a₀ + K.d (n + 2) (n + 1) e', ?_, ?_⟩
  · rw [map_add, ha₀]
    have hzero := ConcreteCategory.congr_hom (K.d_toCycles (n + 2) (n + 1) n) e'
    change K.toCycles (n + 1) n (K.d (n + 2) (n + 1) e') = 0 at hzero
    rw [hzero, add_zero]
  · have hcomm := ConcreteCategory.congr_hom (f.comm (n + 2) (n + 1)) e'
    change L.d (n + 2) (n + 1) (f.f (n + 2) e') =
      f.f (n + 1) (K.d (n + 2) (n + 1) e') at hcomm
    rw [map_add, ← hcomm, he']
    change f.f (n + 1) a₀ + L.d (n + 2) (n + 1) e = b
    rw [he]
    dsimp only [δ]
    abel

/-- A coherent family of homologically trivial cycles has coherent actual
primitives if the next homology groups vanish. -/
theorem exists_coherent_boundary_primitives
    (C : ℕ → ChainComplex (ModuleCat.{v} R) ℕ) (p : ∀ i, C (i + 1) ⟶ C i)
    (n : ℕ) (hsurj : ∀ i, Function.Surjective ((p i).f (n + 2)))
    (hvanish : ∀ i, IsZero ((C i).homology (n + 1)))
    (z : ∀ i, (C i).cycles n)
    (hz : ∀ i, (C i).homologyπ n (z i) = 0)
    (hcoh : ∀ i, cyclesMap (p i) n (z (i + 1)) = z i) :
    ∃ b : ∀ i, (C i).X (n + 1),
      (∀ i, (C i).toCycles (n + 1) n (b i) = z i) ∧
      ∀ i, (p i).f (n + 1) (b (i + 1)) = b i := by
  classical
  let V (i : ℕ) := {b : (C i).X (n + 1) // (C i).toCycles (n + 1) n b = z i}
  have step : ∀ i, ∀ b : V i, ∃ a : V (i + 1), (p i).f (n + 1) a.val = b.val := by
    intro i b
    obtain ⟨a, ha, hmap⟩ := exists_boundary_primitive_lifting (p i) n (hsurj i)
      (hvanish i) (z (i + 1)) (hz (i + 1)) b.val
      (b.property.trans (hcoh i).symm)
    exact ⟨⟨a, ha⟩, hmap⟩
  choose next hnext using step
  obtain ⟨b₀, hb₀⟩ := exists_toCycles_eq_of_homologyπ_eq_zero (C 0) n (z 0) (hz 0)
  let b : ∀ i, V i := Nat.rec ⟨b₀, hb₀⟩ next
  exact ⟨fun i => (b i).val, fun i => (b i).property, fun i => hnext i (b i)⟩

/-- Two coherent cycle families representing the same levelwise homology
classes differ by a coherent boundary when the next homology vanishes. -/
theorem coherent_cycles_equal_mod_boundary
    (C : ℕ → ChainComplex (ModuleCat.{v} R) ℕ) (p : ∀ i, C (i + 1) ⟶ C i)
    (n : ℕ) (hsurj : ∀ i, Function.Surjective ((p i).f (n + 2)))
    (hvanish : ∀ i, IsZero ((C i).homology (n + 1)))
    (z w : ∀ i, (C i).cycles n)
    (hz : ∀ i, cyclesMap (p i) n (z (i + 1)) = z i)
    (hw : ∀ i, cyclesMap (p i) n (w (i + 1)) = w i)
    (hclass : ∀ i, (C i).homologyπ n (z i) = (C i).homologyπ n (w i)) :
    ∃ b : ∀ i, (C i).X (n + 1),
      (∀ i, (C i).toCycles (n + 1) n (b i) = z i - w i) ∧
      ∀ i, (p i).f (n + 1) (b (i + 1)) = b i := by
  apply exists_coherent_boundary_primitives C p n hsurj hvanish (fun i => z i - w i)
  · intro i
    rw [map_sub, hclass i, sub_self]
  · intro i
    rw [map_sub, hz i, hw i]

/-- Joint injectivity of projections on chains implies joint injectivity on
their native cycle objects. -/
theorem chain_cycles_projections_jointly_injective
    (D : ChainComplex (ModuleCat.{v} R) ℕ)
    (C : ℕ → ChainComplex (ModuleCat.{v} R) ℕ) (q : ∀ i, D ⟶ C i) (n : ℕ)
    (hinj : Function.Injective (fun a : D.X n => fun i => (q i).f n a)) :
    Function.Injective (fun z : D.cycles n => fun i => cyclesMap (q i) n z) := by
  intro z w h
  apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
  apply hinj
  funext i
  have hz := ConcreteCategory.congr_hom (cyclesMap_i (q i) n) z
  have hw := ConcreteCategory.congr_hom (cyclesMap_i (q i) n) w
  exact hz.symm.trans ((congrArg ((C i).iCycles n) (congrFun h i)).trans hw)

/-- A chain complex identified degreewise with the coherent chains of the
tower realizes every coherent family of native homology classes. -/
theorem exists_homology_class_of_coherent_classes
    (D : ChainComplex (ModuleCat.{v} R) ℕ)
    (C : ℕ → ChainComplex (ModuleCat.{v} R) ℕ) (p : ∀ i, C (i + 1) ⟶ C i)
    (q : ∀ i, D ⟶ C i) (n : ℕ)
    (hsurj : ∀ i, Function.Surjective ((p i).f (n + 1)))
    (hinj : ∀ k, Function.Injective (fun a : D.X k => fun i => (q i).f k a))
    (hlift : ∀ (k : ℕ) (a : ∀ i, (C i).X k),
      (∀ i, (p i).f k (a (i + 1)) = a i) →
      ∃ b : D.X k, ∀ i, (q i).f k b = a i)
    (c : ∀ i, (C i).homology n)
    (hc : ∀ i, homologyMap (p i) n (c (i + 1)) = c i) :
    ∃ a : D.homology n, ∀ i, homologyMap (q i) n a = c i := by
  obtain ⟨z, hz, hcoh⟩ := exists_coherent_cycle_representatives C p n hsurj c hc
  have hchains : ∀ i, (p i).f n ((C (i + 1)).iCycles n (z (i + 1))) =
      (C i).iCycles n (z i) := by
    intro i
    have h := ConcreteCategory.congr_hom (cyclesMap_i (p i) n) (z (i + 1))
    exact h.symm.trans (congrArg ((C i).iCycles n) (hcoh i))
  obtain ⟨b, hb⟩ := hlift n (fun i => (C i).iCycles n (z i)) hchains
  let k := (ComplexShape.down ℕ).next n
  have hdb : D.d n k b = 0 := by
    apply hinj k
    funext i
    change (q i).f k (D.d n k b) = (q i).f k 0
    rw [map_zero]
    have h := ConcreteCategory.congr_hom ((q i).comm n k) b
    change (C i).d n k ((q i).f n b) = (q i).f k (D.d n k b) at h
    rw [← h, hb i]
    exact ConcreteCategory.congr_hom ((C i).iCycles_d n k) (z i)
  let w : D.cycles n := D.cyclesMk b k rfl hdb
  have hw : D.iCycles n w = b := D.i_cyclesMk b k rfl hdb
  have hmap : ∀ i, cyclesMap (q i) n w = z i := by
    intro i
    apply (ModuleCat.mono_iff_injective ((C i).iCycles n)).mp inferInstance
    have h := ConcreteCategory.congr_hom (cyclesMap_i (q i) n) w
    exact h.trans (by
      change (q i).f n (D.iCycles n w) = (C i).iCycles n (z i)
      rw [hw, hb i])
  refine ⟨D.homologyπ n w, fun i => ?_⟩
  rw [← chainHomologyπ_naturality_apply, hmap i, hz i]

/-- If the next levelwise homology vanishes, projections determine a native
homology class of a complex of coherent chains uniquely. -/
theorem homology_class_eq_of_coherent_projections
    (D : ChainComplex (ModuleCat.{v} R) ℕ)
    (C : ℕ → ChainComplex (ModuleCat.{v} R) ℕ) (p : ∀ i, C (i + 1) ⟶ C i)
    (q : ∀ i, D ⟶ C i) (n : ℕ)
    (hsurj : ∀ i, Function.Surjective ((p i).f (n + 2)))
    (hvanish : ∀ i, IsZero ((C i).homology (n + 1)))
    (hq : ∀ i, q (i + 1) ≫ p i = q i)
    (hinj : ∀ k, Function.Injective (fun a : D.X k => fun i => (q i).f k a))
    (hlift : ∀ (k : ℕ) (a : ∀ i, (C i).X k),
      (∀ i, (p i).f k (a (i + 1)) = a i) →
      ∃ b : D.X k, ∀ i, (q i).f k b = a i)
    (a b : D.homology n)
    (hab : ∀ i, homologyMap (q i) n a = homologyMap (q i) n b) : a = b := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (D.homologyπ n)).mp inferInstance a
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective (D.homologyπ n)).mp inferInstance b
  have coh (z : D.cycles n) :
      ∀ i, cyclesMap (p i) n (cyclesMap (q (i + 1)) n z) = cyclesMap (q i) n z := by
    intro i
    have h := congrArg (fun f : D ⟶ C i => cyclesMap f n) (hq i)
    rw [cyclesMap_comp] at h
    exact ConcreteCategory.congr_hom h z
  have hclass : ∀ i, (C i).homologyπ n (cyclesMap (q i) n z) =
      (C i).homologyπ n (cyclesMap (q i) n w) := by
    intro i
    rw [chainHomologyπ_naturality_apply, chainHomologyπ_naturality_apply, hz, hw]
    exact hab i
  obtain ⟨t, ht, hcoht⟩ := coherent_cycles_equal_mod_boundary C p n hsurj hvanish
    (fun i => cyclesMap (q i) n z) (fun i => cyclesMap (q i) n w) (coh z) (coh w) hclass
  obtain ⟨v, hv⟩ := hlift (n + 1) t hcoht
  have hboundary : D.toCycles (n + 1) n v = z - w := by
    apply chain_cycles_projections_jointly_injective D C q n (hinj n)
    funext i
    change cyclesMap (q i) n (D.toCycles (n + 1) n v) = cyclesMap (q i) n (z - w)
    rw [chainToCycles_naturality_apply, hv i, ht i, map_sub]
  have hzero := ConcreteCategory.congr_hom (D.toCycles_comp_homologyπ (n + 1) n) v
  change D.homologyπ n (D.toCycles (n + 1) n v) = 0 at hzero
  rw [hboundary, map_sub, hz, hw] at hzero
  exact sub_eq_zero.mp hzero

/-- A coherent homology family determines a unique native homology class in
an actual degreewise inverse-limit model when the next homology groups
vanish. The hypotheses `hinj` and `hlift` are the explicit chain-level limit
property, and must be proved for the chosen model. -/
theorem existsUnique_homology_class_of_coherent_classes
    (D : ChainComplex (ModuleCat.{v} R) ℕ)
    (C : ℕ → ChainComplex (ModuleCat.{v} R) ℕ) (p : ∀ i, C (i + 1) ⟶ C i)
    (q : ∀ i, D ⟶ C i) (n : ℕ)
    (hsurj : ∀ i k, Function.Surjective ((p i).f k))
    (hvanish : ∀ i, IsZero ((C i).homology (n + 1)))
    (hq : ∀ i, q (i + 1) ≫ p i = q i)
    (hinj : ∀ k, Function.Injective (fun a : D.X k => fun i => (q i).f k a))
    (hlift : ∀ (k : ℕ) (a : ∀ i, (C i).X k),
      (∀ i, (p i).f k (a (i + 1)) = a i) →
      ∃ b : D.X k, ∀ i, (q i).f k b = a i)
    (c : ∀ i, (C i).homology n)
    (hc : ∀ i, homologyMap (p i) n (c (i + 1)) = c i) :
    ∃! a : D.homology n, ∀ i, homologyMap (q i) n a = c i := by
  obtain ⟨a, ha⟩ := exists_homology_class_of_coherent_classes D C p q n
    (fun i => hsurj i (n + 1)) hinj hlift c hc
  refine ⟨a, ha, fun b hb => ?_⟩
  exact homology_class_eq_of_coherent_projections D C p q n
    (fun i => hsurj i (n + 2)) hvanish hq hinj hlift b a
    (fun i => (hb i).trans (ha i).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CoherentLifting.Cycles
