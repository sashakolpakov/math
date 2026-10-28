import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Generators
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Kernels

/-! # Split Scalar -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.SplitScalar.Construction

noncomputable section

section

/-! The principal scalar has the prescribed subgroup kernels on all
test schemes. These are equalities of actual subgroup functors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {g N q : ℕ} [Fact q.Prime] {S : Scheme}

def trivialPointSubgroup (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) : TateComparison.Subgroups.PointSubgroup B where
  atTest _ := ⊥
  pullback_mem f x hx := by
    change x = 1 at hx
    change f ≫ x = 1
    rw [hx, MonObj.comp_one]

/-- The norm identity bounds the entire scheme-theoretic scalar kernel. -/
theorem scalar_kernel_killed_by_norm
    (B : TateComparison.PEL.PELFamilyData (𝓞 E) g N S) (b : 𝓞 E) (m : ℕ)
    (hnorm : b * IsCMField.ringOfIntegersComplexConj E b = m)
    (T : Over S) (x : T ⟶ B.abelian.scheme)
    (hx : x ≫ Scalar.Construction.scalarMap B b = 1) : x ^ m = 1 := by
  have hc := (Scalar.Construction.scalarMap_complements B b m hnorm).1
  have h := congrArg (fun f => x ≫ f) hc
  rw [← Category.assoc, hx, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at h
  exact h.symm

omit [NumberField E] [IsCMField E] in
/-- On a selected block the scalar kills the whole block; on the opposite
block its kernel is trivial. Both assertions include nonreduced tests. -/
theorem scalar_side_kernel
    (B : TateComparison.PEL.PELFamilyData (𝓞 E) g N S) (χ : 𝓞 E →+* ℤ_[q])
    (b : 𝓞 E) (n : ℕ) (selected : Prop) [Decidable selected]
    (u : ℤ_[q]ˣ) (hlocal : χ b = (q : ℤ_[q]) ^ (if selected then n else 0) * u) :
    (TateComparison.Subgroups.PointSubgroup.kernel (Scalar.Construction.scalarMap B b)).inf (TateComparison.Subgroups.splitBlock B χ n) =
      if selected then TateComparison.Subgroups.splitBlock B χ n else trivialPointSubgroup B.abelian := by
  apply TateComparison.Subgroups.PointSubgroup.ext
  intro T
  apply Subgroup.ext
  intro x
  by_cases hs : selected
  · rw [ite_eq_left hs]
    change (x ≫ Scalar.Construction.scalarMap B b = 1 ∧ x ∈ (TateComparison.Subgroups.splitBlock B χ n).atTest T) ↔ _
    constructor
    · exact And.right
    · intro hx
      refine ⟨?_, hx⟩
      have hk := Kernels.Construction.scalar_kernel_on_splitBlock B χ b n (if selected then n else 0)
        u hlocal T x hx
      rw [ite_eq_left hs] at hk
      exact hk.mpr hx.1
  · rw [ite_eq_right hs]
    change (x ≫ Scalar.Construction.scalarMap B b = 1 ∧ x ∈ (TateComparison.Subgroups.splitBlock B χ n).atTest T) ↔ x = 1
    constructor
    · rintro ⟨hk, hx⟩
      have he := (Kernels.Construction.scalar_kernel_on_splitBlock B χ b n (if selected then n else 0)
        u hlocal T x hx).mp hk
      simpa only [ite_eq_right hs, pow_zero, pow_one] using he
    · rintro rfl
      exact ⟨MonObj.one_comp _, (TateComparison.Subgroups.splitBlock B χ n).atTest T |>.one_mem⟩

variable {K : Type} [Field K] [NumberField K] {s : ℕ}

/-- Finiteness now gives a scalar whose exact norm, complete marking, and all
chosen and opposite kernel blocks are established from TateComparison's input data. -/
theorem exists_marked_scalar_with_side_kernels
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime) (hlevel : 0 < D.level)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (hFiniteness : Arithmetic.Construction.PrincipalizationInput E) (side : Fin s → Bool) :
    ∃ (n : ℕ) (b : 𝓞 E), 0 < n ∧ b ≠ 0 ∧
      b * IsCMField.ringOfIntegersComplexConj E b = (q : 𝓞 E) ^ n ∧
      Marking.Construction.levelReduction E D.level b = 1 ∧
      ∀ (S : Scheme) (B : TateComparison.PEL.PELFamilyData (𝓞 E) (3 * s) D.level S)
        (v : Fin s) (w : Bool),
        (TateComparison.Subgroups.PointSubgroup.kernel (Scalar.Construction.scalarMap B b)).inf
          (TateComparison.Subgroups.splitBlock B (D.localCharacter (v, w)) n) =
        if w = side v then TateComparison.Subgroups.splitBlock B (D.localCharacter (v, w)) n
        else trivialPointSubgroup B.abelian := by
  obtain ⟨n, b, hn, hb, hnorm, hmark, hlocal⟩ :=
    Generators.Construction.marked_side_generator_local D hgood hlevel hdegree hFiniteness side
  refine ⟨n, b, hn, hb, hnorm, hmark, ?_⟩
  intro S B v w
  obtain ⟨u, hu⟩ := hlocal v w
  exact scalar_side_kernel B (D.localCharacter (v, w)) b n (w = side v) u hu

end

section

/-! Integral lifts of the split residue idempotents give projectors on the
actual torsion functor. Their sum is the identity on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

def residueProjector (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime) (h : ℕ) (i : Fin s × Bool) : 𝓞 E :=
  (SideResidues.Construction.residueCoordinates_surjective D hgood h (Pi.single i 1)).choose

theorem residueProjector_spec (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime) (h : ℕ) (i : Fin s × Bool) :
    SideResidues.Construction.residueCoordinates D h (residueProjector D hgood h i) = Pi.single i 1 :=
  (SideResidues.Construction.residueCoordinates_surjective D hgood h (Pi.single i 1)).choose_spec

omit [NumberField E] [IsCMField E] in
/-- Scalar actions on N-torsion depend only on the residue modulo N. -/
theorem scalarMap_eq_of_congruence {S : Scheme} {g N : ℕ}
    (B : TateComparison.PEL.PELFamilyData (𝓞 E) g N S) (b c : 𝓞 E) (m : ℕ)
    (hbc : b - c ∈ Ideal.span {(m : 𝓞 E)})
    (T : Over S) (x : T ⟶ B.abelian.scheme) (hx : x ^ m = 1) :
    x ≫ Scalar.Construction.scalarMap B b = x ≫ Scalar.Construction.scalarMap B c := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hbc
  have hb : b = c + r * (m : 𝓞 E) := by
    rw [mul_comm r, ← hr]
    abel
  unfold Scalar.Construction.scalarMap
  rw [hb, map_add, TateComparison.BaseChange.endSchemeMap_add, MonObj.comp_mul, map_mul,
    TateComparison.BaseChange.endSchemeMap_mul, map_natCast, Scalar.Construction.scalar_natCast_schemeMap,
    ← Category.assoc, MonObj.comp_pow, Category.comp_id,
    hx, MonObj.one_comp, mul_one]

/-- The supplied completion coordinates determine the scalar action on
q-power torsion, without a separately assumed eigenspace decomposition. -/
theorem scalarMap_eq_of_residues (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s)
    {S : Scheme} {g N : ℕ} (B : TateComparison.PEL.PELFamilyData (𝓞 E) g N S)
    (b c : 𝓞 E) (h : ℕ) (hbc : SideResidues.Construction.residueCoordinates D h b = SideResidues.Construction.residueCoordinates D h c)
    (T : Over S) (x : T ⟶ B.abelian.scheme) (hx : x ^ (q ^ h) = 1) :
    x ≫ Scalar.Construction.scalarMap B b = x ≫ Scalar.Construction.scalarMap B c := by
  apply scalarMap_eq_of_congruence B b c (q ^ h) ?_ T x hx
  change b - c ∈ SideResidues.Construction.qPowerIdeal E q h
  rw [← SideResidues.Construction.residueCoordinates_kernel D hgood hdegree h]
  change SideResidues.Construction.residueCoordinates D h (b - c) = 0
  rw [map_sub, hbc, sub_self]

omit [NumberField E] [IsCMField E] in
theorem scalarMap_sum_points {S : Scheme} {g N : ℕ}
    (B : TateComparison.PEL.PELFamilyData (𝓞 E) g N S) {Idx : Type*} (t : Finset Idx) (b : Idx → 𝓞 E)
    (T : Over S) (x : T ⟶ B.abelian.scheme) :
    x ≫ Scalar.Construction.scalarMap B (∑ i ∈ t, b i) = ∏ i ∈ t, x ≫ Scalar.Construction.scalarMap B (b i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Scalar.Construction.scalarMap, TateComparison.BaseChange.endSchemeMap_zero, MonObj.comp_one]
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    change x ≫ TateComparison.End.endSchemeMap _ (B.action (b i + ∑ j ∈ t, b j)) = _
    rw [map_add, TateComparison.BaseChange.endSchemeMap_add, MonObj.comp_mul]
    exact congrArg (fun z => (x ≫ Scalar.Construction.scalarMap B (b i)) * z) ih

/-- The split residue projectors sum to the identity on the full q-power
torsion subgroup, as an equality on every test scheme. -/
theorem residueProjector_sum_points (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s)
    {S : Scheme} {g N : ℕ} (B : TateComparison.PEL.PELFamilyData (𝓞 E) g N S)
    (h : ℕ) (T : Over S) (x : T ⟶ B.abelian.scheme) (hx : x ^ (q ^ h) = 1) :
    ∏ i : Fin s × Bool, x ≫ Scalar.Construction.scalarMap B (residueProjector D hgood h i) = x := by
  rw [← scalarMap_sum_points]
  have hr : SideResidues.Construction.residueCoordinates D h (∑ i, residueProjector D hgood h i) =
      SideResidues.Construction.residueCoordinates D h 1 := by
    rw [map_sum, map_one]
    simp only [residueProjector_spec]
    ext i
    simp
  rw [scalarMap_eq_of_residues D hgood hdegree B _ 1 h hr T x hx]
  rw [Scalar.Construction.scalarMap, map_one, TateComparison.BaseChange.endSchemeMap_one, Category.comp_id]

/-- Each integral residue projector lands in the specified split block. -/
theorem residueProjector_mem_splitBlock (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s)
    {S : Scheme} {g N : ℕ} (B : TateComparison.PEL.PELFamilyData (𝓞 E) g N S)
    (h : ℕ) (i : Fin s × Bool)
    (T : Over S) (x : T ⟶ B.abelian.scheme) (hx : x ^ (q ^ h) = 1) :
    x ≫ Scalar.Construction.scalarMap B (residueProjector D hgood h i) ∈
      (TateComparison.Subgroups.splitBlock B (D.localCharacter i) h).atTest T := by
  classical
  let e := residueProjector D hgood h i
  refine ⟨?_, ?_⟩
  · rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  · intro b
    let k := (SideResidues.Construction.residueCoordinates D h b i).val
    have hr : SideResidues.Construction.residueCoordinates D h (b * e) =
        SideResidues.Construction.residueCoordinates D h ((k : 𝓞 E) * e) := by
      rw [map_mul, map_mul, map_natCast]
      dsimp [e]
      rw [residueProjector_spec]
      ext j
      change SideResidues.Construction.residueCoordinates D h b j * (Pi.single i 1 : Fin s × Bool → ZMod (q ^ h)) j =
        (k : ZMod (q ^ h)) * (Pi.single i 1 : Fin s × Bool → ZMod (q ^ h)) j
      by_cases hj : j = i
      · subst j
        simp [k]
      · simp [hj]
    have he := scalarMap_eq_of_residues D hgood hdegree B (b * e) ((k : 𝓞 E) * e)
      h hr T x hx
    unfold Scalar.Construction.scalarMap at he
    rw [map_mul, TateComparison.BaseChange.endSchemeMap_mul, map_mul, TateComparison.BaseChange.endSchemeMap_mul,
      map_natCast, Scalar.Construction.scalar_natCast_schemeMap, ← Category.assoc,
      ← Category.assoc, MonObj.comp_pow, Category.comp_id] at he
    exact he

end

section

/-! Distinct local characters force equivariant rational Tate maps to
preserve the independent blocks. This reconstructs full preimage lattices
from the chosen and opposite projections in TateComparison. -/

section Linear

variable {Idx R L V : Type*} [Fintype Idx] [DecidableEq Idx]
  [Field L] [AddCommGroup V] [Module L V]
  (χ : R → Idx → L)
  (hsep : ∀ i j : Idx, i ≠ j → ∃ b : R, χ b i ≠ χ b j)
  (F : (Idx → V) →ₗ[L] (Idx → V))
  (hF : ∀ (b : R) (x : Idx → V),
    F (fun i => χ b i • x i) = fun i => χ b i • F x i)

include hsep hF

omit [Fintype Idx] in
/-- An equivariant map has no component between different characters. -/
theorem intertwiner_single_off_diagonal (i j : Idx) (hij : i ≠ j) (v : V) :
    F (Pi.single i v) j = 0 := by
  obtain ⟨b, hb⟩ := hsep i j hij
  have he := congrFun (hF b (Pi.single i v)) j
  have hx : (fun k => χ b k • (Pi.single i v : Idx → V) k) = χ b i • Pi.single i v := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  rw [hx, map_smul] at he
  change χ b i • F (Pi.single i v) j = χ b j • F (Pi.single i v) j at he
  have hz : (χ b i - χ b j) • F (Pi.single i v) j = 0 := by
    rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hb)

/-- Every output coordinate depends only on the matching input coordinate. -/
theorem intertwiner_coordinate (x : Idx → V) (j : Idx) :
    F x j = F (Pi.single j (x j)) j := by
  have hx : x = ∑ i : Idx, Pi.single i (x i) := by
    ext i
    simp
  calc
    F x j = ∑ i : Idx, F (Pi.single i (x i)) j := by
      conv_lhs => rw [hx]
      rw [map_sum, Finset.sum_apply]
    _ = F (Pi.single j (x j)) j := by
      apply Finset.sum_eq_single j
      · intro i _ hij
        exact intertwiner_single_off_diagonal χ hsep F hF i j hij (x i)
      · simp

end Linear

variable {Idx R V : Type*} [Fintype Idx] [DecidableEq Idx]
  [CommRing R] [AddCommGroup V] [Module R V]

/-- A submodule stable under the coordinate projectors is determined by
its projected submodules; no equality of full lattices is assumed. -/
theorem split_submodule_le_of_projections (P Q : Submodule R (Idx → V))
    (hQ : ∀ x ∈ Q, ∀ i, Pi.single i (x i) ∈ Q)
    (hproj : ∀ i, P.map (LinearMap.proj i) ≤ Q.map (LinearMap.proj i)) : P ≤ Q := by
  intro x hx
  have hs (i : Idx) : Pi.single i (x i) ∈ Q := by
    have hi : x i ∈ P.map (LinearMap.proj i) := Submodule.mem_map_of_mem hx
    obtain ⟨y, hy, he⟩ := hproj i hi
    have hys := hQ y hy i
    change y i = x i at he
    rw [he] at hys
    exact hys
  have he : ∑ i : Idx, Pi.single i (x i) = x := by ext i; simp
  rw [← he]
  exact Submodule.sum_mem Q (fun i _ => hs i)

theorem split_submodule_eq_of_projections (P Q : Submodule R (Idx → V))
    (hP : ∀ x ∈ P, ∀ i, Pi.single i (x i) ∈ P)
    (hQ : ∀ x ∈ Q, ∀ i, Pi.single i (x i) ∈ Q)
    (hproj : ∀ i, P.map (LinearMap.proj i) = Q.map (LinearMap.proj i)) : P = Q := by
  apply le_antisymm
  · exact split_submodule_le_of_projections P Q hQ (fun i => (hproj i).le)
  · exact split_submodule_le_of_projections Q P hP (fun i => (hproj i).ge)

end

/-! The actual split completion coordinates separate every pair of
characters. Integral residue idempotents supply explicit witnesses. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

theorem localCharacter_separates (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime) (i j : Fin s × Bool) (hij : i ≠ j) :
    ∃ b : NumberField.RingOfIntegers E,
      (D.localCharacter i b : ℚ_[q]) ≠ (D.localCharacter j b : ℚ_[q]) := by
  have : Fact ((q ^ 1).Prime) := ⟨by simpa only [pow_one] using (Fact.out : q.Prime)⟩
  let b := residueProjector D hgood 1 i
  refine ⟨b, ?_⟩
  intro he
  have he' : D.localCharacter i b = D.localCharacter j b := Subtype.val_injective he
  have hr : SideResidues.Construction.residueCoordinates D 1 b i = SideResidues.Construction.residueCoordinates D 1 b j :=
    congrArg (PadicInt.toZModPow 1) he'
  have hi : SideResidues.Construction.residueCoordinates D 1 b i = 1 := by
    change SideResidues.Construction.residueCoordinates D 1 (residueProjector D hgood 1 i) i = 1
    rw [residueProjector_spec]
    simp
  have hj : SideResidues.Construction.residueCoordinates D 1 b j = 0 := by
    change SideResidues.Construction.residueCoordinates D 1 (residueProjector D hgood 1 i) j = 0
    rw [residueProjector_spec]
    simp [hij.symm]
  exact one_ne_zero (hi.symm.trans (hr.trans hj))

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.SplitScalar.Construction
