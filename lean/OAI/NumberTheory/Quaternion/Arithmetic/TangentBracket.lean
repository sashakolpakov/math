import OAI.NumberTheory.Quaternion.Arithmetic.AlgebraicDifferential
import OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroTangent

/-! # Tangent Bracket -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.TangentBracket

noncomputable section

section

/-! Analytic tangent directions to a local subgroup lie in the actual
algebraic Lie algebra of the connected matrix group. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroTangent.Construction

attribute [local instance] LieRing.ofAssociativeRing

section

variable {K : Type} [NontriviallyNormedField K] [CharZero K] {n : ℕ}

theorem matrixTangentSpan_le_infinitesimalStabilizer
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup K n) (hG : G.IsGeometricallyConnected)
    (H : Subgroup G.RationalPoints) :
    TangentCone.matrixTangentSpan G (RingHom.id K) H ≤ (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule := by
  intro A hA
  apply (ArithmeticGroups.Lattices.CharZeroTangent.Construction.mem_infinitesimalStabilizer_iff_tangent G hG A).mpr
  intro p hp
  apply AlgebraicDifferential.matrixTangentSpan_satisfies_infinitesimal_equations G (RingHom.id K) H p _ hA
  intro g _
  exact hp K (RingHom.id K) g

theorem matrixTangentSpan_le_baseChange_infinitesimalStabilizer
    {F : Type} [Field F] [CharZero F]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected)
    (ι : F →+* K) (H : Subgroup (G.Points ι)) :
    TangentCone.matrixTangentSpan G ι H ≤ (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G ι)).toSubmodule := by
  let : Algebra F K := ι.toAlgebra
  have hc := ArithmeticGroups.Lattices.ConnectedBaseChange.Construction.geometrically_connected_baseChange G hG (K := K)
  exact matrixTangentSpan_le_infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G ι) hc H

end

open scoped _root_.NumberField
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
variable (v : HeightOneSpectrum (𝓞 F))

theorem finite_localArithmetic_tangentSpan_nonzero
    (hd : ¬ IsDiscrete (Closure.localArithmeticSubgroup G S (Sum.inr v) :
      Set (LocalAdeles.LocalPoints G (Sum.inr v)))) :
    TangentCone.matrixTangentSpan G (LocalAdeles.localEmbedding (Sum.inr v))
      (Closure.localArithmeticSubgroup G S (Sum.inr v)).topologicalClosure ≠ ⊥ := by
  let : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  apply TangentCone.matrixTangentSpan_nonzero (K := v.adicCompletion F)
  intro hc
  exact hd (hc.mono (Closure.localArithmeticSubgroup G S (Sum.inr v)).le_topologicalClosure)

theorem finite_localArithmetic_tangentSpan_le_lie
    (hG : G.IsGeometricallyConnected) :
    TangentCone.matrixTangentSpan G (LocalAdeles.localEmbedding (Sum.inr v))
        (Closure.localArithmeticSubgroup G S (Sum.inr v)).topologicalClosure ≤
      (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (LocalAdeles.localEmbedding (Sum.inr v)))).toSubmodule := by
  let : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  exact matrixTangentSpan_le_baseChange_infinitesimalStabilizer (K := v.adicCompletion F)
    G hG (LocalAdeles.localEmbedding (Sum.inr v)) (Closure.localArithmeticSubgroup G S (Sum.inr v)).topologicalClosure

end

section

/-! Taking limits of conjugations gives commutators of tangent directions.
This supplies the Lie-bracket step for invariant local tangent spaces. -/

open scoped Classical
open Set Filter _root_.Topology

section

theorem conjugation_displacement {R : Type*} [Ring R] (M N X : R) (hMN : M * N = 1) :
    M * X * N - X = ((M - 1) * X - X * (M - 1)) * N := by
  calc
    _ = (M * X - X * M) * N := by rw [sub_mul, mul_assoc X M N, hMN, mul_one]
    _ = _ := by congr 1; noncomm_ring

variable {F K : Type} [Field F] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
variable {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)

theorem scaled_conjugation_displacement (g : G.Points ι)
    (X : Matrix (Fin n) (Fin n) K) (c : K) :
    c • (TangentCone.matrixConjugation G ι g X - X) =
      ((c • ((g.val : Matrix (Fin n) (Fin n) K) - 1)) * X -
        X * (c • ((g.val : Matrix (Fin n) (Fin n) K) - 1))) *
          ((g⁻¹).val : Matrix (Fin n) (Fin n) K) := by
  have hgi : (g.val : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹).val : Matrix (Fin n) (Fin n) K) = 1 := by
    change (((g * g⁻¹).val : ArithmeticGroups.Lattices.Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) = 1
    rw [mul_inv_cancel]
    rfl
  change c • (_ * X * _ - X) = _
  rw [conjugation_displacement _ _ X hgi]
  rw [← Matrix.smul_mul, smul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul]

/-- An invariant closed linear space is stable under commutators with
tangent directions to the acting subgroup. -/
theorem tangent_commutator_mem_of_conjugation_invariant
    (H : Subgroup (G.Points ι))
    (W : Submodule K (Matrix (Fin n) (Fin n) K))
    (hclosed : IsClosed (W : Set (Matrix (Fin n) (Fin n) K)))
    (hinvariant : ∀ g ∈ H, MapsTo (TangentCone.matrixConjugation G ι g)
      (W : Set (Matrix (Fin n) (Fin n) K)) (W : Set (Matrix (Fin n) (Fin n) K)))
    {X Y : Matrix (Fin n) (Fin n) K} (hX : X ∈ W) (hY : Y ∈ TangentCone.matrixTangentCone G ι H) :
    Y * X - X * Y ∈ W := by
  obtain ⟨α, l, hl, c, d, hd, hs, hcd⟩ := exists_fun_of_mem_tangentConeAt hY
  have hM : Tendsto (fun a => (1 : Matrix (Fin n) (Fin n) K) + d a) l (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hd
  have hi : Tendsto (fun a => ((1 : Matrix (Fin n) (Fin n) K) + d a).adjugate) l (𝓝 1) := by
    simpa only [Matrix.adjugate_one, Function.comp_def, id_eq] using
      (continuous_id.matrix_adjugate.tendsto 1).comp hM
  let z := fun a => ((c a • d a) * X - X * (c a • d a)) * (1 + d a).adjugate
  have hz : Tendsto z l (𝓝 (Y * X - X * Y)) := by
    simpa only [Matrix.mul_one] using
      ((hcd.mul tendsto_const_nhds).sub (tendsto_const_nhds.mul hcd)).mul hi
  apply hclosed.mem_of_tendsto hz
  filter_upwards [hs] with a ha
  obtain ⟨g, hg, hge⟩ := ha
  change (g.val : Matrix (Fin n) (Fin n) K) = 1 + d a at hge
  have hm := W.smul_mem (c a) (W.sub_mem (hinvariant g hg hX) hX)
  rw [scaled_conjugation_displacement] at hm
  have hginv : ((g⁻¹).val : Matrix (Fin n) (Fin n) K) = (1 + d a).adjugate := by
    calc
      _ = (g.val : Matrix (Fin n) (Fin n) K).adjugate := rfl
      _ = _ := congrArg Matrix.adjugate hge
  have hdg : (g.val : Matrix (Fin n) (Fin n) K) - 1 = d a := by
    simpa only [add_sub_cancel_left] using
      congrArg (fun M : Matrix (Fin n) (Fin n) K => M - 1) hge
  change z a ∈ W
  dsimp only [z]
  simpa only [hdg, hginv] using hm

theorem tangentSpan_commutator_mem_of_conjugation_invariant
    (H : Subgroup (G.Points ι)) (W : Submodule K (Matrix (Fin n) (Fin n) K))
    (hclosed : IsClosed (W : Set (Matrix (Fin n) (Fin n) K)))
    (hinvariant : ∀ g ∈ H, MapsTo (TangentCone.matrixConjugation G ι g)
      (W : Set (Matrix (Fin n) (Fin n) K)) (W : Set (Matrix (Fin n) (Fin n) K)))
    {X Y : Matrix (Fin n) (Fin n) K} (hX : X ∈ W) (hY : Y ∈ TangentCone.matrixTangentSpan G ι H) :
    Y * X - X * Y ∈ W := by
  let f : Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K :=
    { toFun Y := Y * X - X * Y
      map_add' Y Z := by simp only [Matrix.add_mul, Matrix.mul_add]; abel
      map_smul' c Y := by simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, RingHom.id_apply] }
  have hle : TangentCone.matrixTangentSpan G ι H ≤ W.comap f := by
    apply Submodule.span_le.mpr
    intro Y hY
    exact tangent_commutator_mem_of_conjugation_invariant G ι H W hclosed hinvariant hX hY
  exact hle hY

theorem matrixTangentSpan_preserved_by_member
    (H : Subgroup (G.Points ι)) (g : G.Points ι) (hg : g ∈ H) :
    MapsTo (TangentCone.matrixConjugation G ι g)
      (TangentCone.matrixTangentSpan G ι H : Set (Matrix (Fin n) (Fin n) K))
      (TangentCone.matrixTangentSpan G ι H : Set (Matrix (Fin n) (Fin n) K)) := by
  have he : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hg)
  have ht := TangentCone.matrixConjugation_mapsTo_tangentCone G ι g H
  rw [he] at ht
  have hle : TangentCone.matrixTangentSpan G ι H ≤
      (TangentCone.matrixTangentSpan G ι H).comap (TangentCone.matrixConjugation G ι g).toLinearMap := by
    apply Submodule.span_le.mpr
    exact fun X hX => Submodule.subset_span (ht hX)
  exact hle

theorem matrixTangentSpan_closed_under_commutator
    (H : Subgroup (G.Points ι))
    (hc : IsClosed (TangentCone.matrixTangentSpan G ι H : Set (Matrix (Fin n) (Fin n) K)))
    {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ TangentCone.matrixTangentSpan G ι H) (hY : Y ∈ TangentCone.matrixTangentSpan G ι H) :
    Y * X - X * Y ∈ TangentCone.matrixTangentSpan G ι H :=
  tangentSpan_commutator_mem_of_conjugation_invariant G ι H _ hc
    (matrixTangentSpan_preserved_by_member G ι H) hX hY

end

attribute [local instance] LieRing.ofAssociativeRing

variable {F K : Type} [Field F] [NontriviallyNormedField K] [CompleteSpace K] {n : ℕ}

/-- The span of the actual tangent cone is a matrix Lie subalgebra over
a complete nontrivially normed field. -/
def matrixTangentLieSubalgebra (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    (H : Subgroup (G.Points ι)) : LieSubalgebra K (Matrix (Fin n) (Fin n) K) :=
  { TangentCone.matrixTangentSpan G ι H with
    lie_mem' := fun {_X _Y} hX hY =>
      matrixTangentSpan_closed_under_commutator G ι H
        (TangentCone.matrixTangentSpan G ι H).closed_of_finiteDimensional hY hX }

@[simp] theorem matrixTangentLieSubalgebra_toSubmodule
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) (H : Subgroup (G.Points ι)) :
    (matrixTangentLieSubalgebra G ι H).toSubmodule = TangentCone.matrixTangentSpan G ι H := rfl

theorem matrixTangentLieSubalgebra_le_baseChange_lie [CharZero F] [CharZero K]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected)
    (ι : F →+* K) (H : Subgroup (G.Points ι)) :
    matrixTangentLieSubalgebra G ι H ≤
      ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G ι) :=
  matrixTangentSpan_le_baseChange_infinitesimalStabilizer G hG ι H

end

section

/-! A commensurated subgroup has a tangent span that is stable under Lie
brackets with tangent directions to its commensurating subgroup. -/

open scoped Classical
open Set _root_.Topology

section

variable {F K : Type} [Field F] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
variable {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)

theorem continuous_matrixConjugation_point
    (X : Matrix (Fin n) (Fin n) K) :
    Continuous (fun g : G.Points ι => TangentCone.matrixConjugation G ι g X) := by
  change Continuous (fun g : G.Points ι =>
    (g.val : Matrix (Fin n) (Fin n) K) * X * ((g⁻¹).val : Matrix (Fin n) (Fin n) K))
  fun_prop

theorem conjugation_invariance_extends_to_closure
    (R : Subgroup (G.Points ι)) (W : Submodule K (Matrix (Fin n) (Fin n) K))
    (hc : IsClosed (W : Set (Matrix (Fin n) (Fin n) K)))
    (hR : ∀ g ∈ R, MapsTo (TangentCone.matrixConjugation G ι g)
      (W : Set (Matrix (Fin n) (Fin n) K)) (W : Set (Matrix (Fin n) (Fin n) K))) :
    ∀ g ∈ R.topologicalClosure, MapsTo (TangentCone.matrixConjugation G ι g)
      (W : Set (Matrix (Fin n) (Fin n) K)) (W : Set (Matrix (Fin n) (Fin n) K)) := by
  intro g hg X hX
  have hs : IsClosed {g : G.Points ι | TangentCone.matrixConjugation G ι g X ∈ W} :=
    hc.preimage (continuous_matrixConjugation_point G ι X)
  exact closure_minimal (fun y hy => hR y hy hX) hs hg

end

section

variable {F K : Type} [Field F] [NontriviallyNormedField K] [CompleteSpace K] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)

theorem tangent_commutator_mem_of_commensurated
    (H R : Subgroup (G.Points ι))
    (hcomm : ∀ g ∈ R, (H.map (MulAut.conj g).toMonoidHom).Commensurable H)
    {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ TangentCone.matrixTangentSpan G ι H.topologicalClosure)
    (hY : Y ∈ TangentCone.matrixTangentSpan G ι R.topologicalClosure) :
    Y * X - X * Y ∈ TangentCone.matrixTangentSpan G ι H.topologicalClosure := by
  let W := TangentCone.matrixTangentSpan G ι H.topologicalClosure
  have hc : IsClosed (W : Set (Matrix (Fin n) (Fin n) K)) := W.closed_of_finiteDimensional
  have hR : ∀ g ∈ R, MapsTo (TangentCone.matrixConjugation G ι g)
      (W : Set (Matrix (Fin n) (Fin n) K)) (W : Set (Matrix (Fin n) (Fin n) K)) := by
    intro g hg
    have ht := TangentCone.matrixConjugation_preserves_closure_tangentCone G ι g H (hcomm g hg)
    have hle : W ≤ W.comap (TangentCone.matrixConjugation G ι g).toLinearMap := by
      apply Submodule.span_le.mpr
      exact fun X hX => Submodule.subset_span (ht hX)
    exact hle
  exact tangentSpan_commutator_mem_of_conjugation_invariant G ι R.topologicalClosure W hc
    (conjugation_invariance_extends_to_closure G ι R W hc hR) hX hY

end

open scoped _root_.NumberField
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
variable (v : HeightOneSpectrum (𝓞 F))

theorem finite_localArithmetic_tangent_ideal
    (hS : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
    {X Y : Matrix (Fin n) (Fin n) (LocalAdeles.Completion (Sum.inr v))}
    (hX : X ∈ TangentCone.matrixTangentSpan G (LocalAdeles.localEmbedding (Sum.inr v))
      (Closure.localArithmeticSubgroup G S (Sum.inr v)).topologicalClosure)
    (hY : Y ∈ TangentCone.matrixTangentSpan G (LocalAdeles.localEmbedding (Sum.inr v))
      (LocalAdeles.diagonalLocal G (Sum.inr v)).range.topologicalClosure) :
    Y * X - X * Y ∈ TangentCone.matrixTangentSpan G (LocalAdeles.localEmbedding (Sum.inr v))
      (Closure.localArithmeticSubgroup G S (Sum.inr v)).topologicalClosure := by
  let : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  apply tangent_commutator_mem_of_commensurated (K := v.adicCompletion F)
    G (LocalAdeles.localEmbedding (Sum.inr v)) (Closure.localArithmeticSubgroup G S (Sum.inr v))
    (LocalAdeles.diagonalLocal G (Sum.inr v)).range _ hX hY
  intro g hg
  obtain ⟨a, rfl⟩ := hg
  have h := Closure.localArithmetic_conjugate_commensurable G S (Sum.inr v) hS a⁻¹
  rw [map_inv, Subgroup.comap_equiv_eq_map_symm'] at h
  have he : (MulAut.conj (LocalAdeles.diagonalLocal G (Sum.inr v) a)⁻¹).symm.toMonoidHom =
      (MulAut.conj (LocalAdeles.diagonalLocal G (Sum.inr v) a)).toMonoidHom := by
    ext x
    simp
  rwa [he] at h

end

section

/-! Tangent directions with a separately specified scalar field. The
closed-subgroup argument must retain this choice when the local field is
a finite extension of its prime local field. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open Set Filter _root_.Topology

section

variable {F K κ : Type} [Field F] [Field K] [Field κ] [Algebra κ K]
variable [TopologicalSpace K] {n : ℕ}

def matrixTangentConeOver (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    (H : Subgroup (G.Points ι)) : Set (Matrix (Fin n) (Fin n) K) :=
  tangentConeAt κ
    ((fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K)) '' (H : Set (G.Points ι))) 1

def matrixTangentSpanOver (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    (H : Subgroup (G.Points ι)) : Submodule κ (Matrix (Fin n) (Fin n) K) :=
  Submodule.span κ (matrixTangentConeOver (κ := κ) G ι H)

theorem matrixTangentConeOver_subset (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    (H : Subgroup (G.Points ι)) : matrixTangentConeOver (κ := κ) G ι H ⊆ TangentCone.matrixTangentCone G ι H :=
  tangentConeAt_mono_field

theorem matrixTangentSpanOver_le_restrictScalars
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) (H : Subgroup (G.Points ι)) :
    matrixTangentSpanOver (κ := κ) G ι H ≤ (TangentCone.matrixTangentSpan G ι H).restrictScalars κ := by
  apply Submodule.span_le.mpr
  exact fun X hX => Submodule.subset_span (matrixTangentConeOver_subset G ι H hX)

variable [IsTopologicalRing K] [T2Space K]

theorem matrixTangentConeOver_closures_eq_of_commensurable
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    {H J : Subgroup (G.Points ι)} (h : H.Commensurable J) :
    matrixTangentConeOver (κ := κ) G ι H.topologicalClosure =
      matrixTangentConeOver (κ := κ) G ι J.topologicalClosure := by
  let f := fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K)
  have hf := (G.points_isClosedEmbedding ι).isEmbedding
  have hn := congrArg (Filter.map f) (ClosureCommensurability.commensurable_closures_nhdsWithin_eq h)
  rw [hf.map_nhdsWithin_eq, hf.map_nhdsWithin_eq] at hn
  have ht := tangentConeAt_congr (𝕜 := κ) hn
  simpa only [f, matrixTangentConeOver, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one] using ht

omit [T2Space K] in
theorem matrixConjugation_mapsTo_tangentConeOver
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    (g : G.Points ι) (H : Subgroup (G.Points ι)) :
    MapsTo (TangentCone.matrixConjugation G ι g) (matrixTangentConeOver (κ := κ) G ι H)
      (matrixTangentConeOver (κ := κ) G ι (H.map (MulAut.conj g).toMonoidHom)) := by
  let e := fun h : G.Points ι => (h.val : Matrix (Fin n) (Fin n) K)
  have himage : TangentCone.matrixConjugation G ι g '' (e '' (H : Set (G.Points ι))) =
      e '' ((H.map (MulAut.conj g).toMonoidHom) : Set (G.Points ι)) := by
    rw [Subgroup.coe_map, image_image, image_image]
    rfl
  have h := TangentCone.continuousLinearMap_mapsTo_tangentCone ((TangentCone.matrixConjugation G ι g).restrictScalars κ)
    (e '' (H : Set (G.Points ι))) 1
  simp only [ContinuousLinearMap.coe_restrictScalars'] at h
  rw [himage, TangentCone.matrixConjugation_one] at h
  exact h

theorem matrixConjugation_preserves_closure_tangentSpanOver
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    (g : G.Points ι) (H : Subgroup (G.Points ι))
    (hc : (H.map (MulAut.conj g).toMonoidHom).Commensurable H) :
    (matrixTangentSpanOver (κ := κ) G ι H.topologicalClosure).map
        ((TangentCone.matrixConjugation G ι g).toLinearMap.restrictScalars κ) ≤
      matrixTangentSpanOver (κ := κ) G ι H.topologicalClosure := by
  have ht := matrixConjugation_mapsTo_tangentConeOver (κ := κ) G ι g H.topologicalClosure
  rw [← TangentCone.closure_map_conj, matrixTangentConeOver_closures_eq_of_commensurable G ι hc] at ht
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  exact fun X hX => Submodule.subset_span (ht hX)

end

variable {F K κ : Type} [Field F] [NontriviallyNormedField K] [NontriviallyNormedField κ]
variable [NormedAlgebra κ K] [ProperSpace K] {n : ℕ}

theorem matrixTangentConeOver_nonzero
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) (H : Subgroup (G.Points ι))
    (hd : ¬ IsDiscrete (H : Set (G.Points ι))) :
    ∃ X ∈ matrixTangentConeOver (κ := κ) G ι H, X ≠ 0 := by
  let : ProperSpace (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (ProperSpace (Fin n → Fin n → K))
  have hacc := TangentCone.accPt_image_of_injective_continuous
    (fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K))
    (G.points_isClosedEmbedding ι).continuous (G.points_isClosedEmbedding ι).injective
    (TangentCone.subgroup_accPt_one_of_not_discrete H hd)
  have hacc' : AccPt (1 : Matrix (Fin n) (Fin n) K)
      (𝓟 ((fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K)) ''
        (H : Set (G.Points ι)))) := by
    simpa only [OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one] using hacc
  obtain ⟨X, hX, hne⟩ := tangentConeAt_nonempty_of_properSpace (𝕜 := κ) hacc'
  exact ⟨X, hX, hne⟩

end

section

/-! A closed subspace stable under a dense set of scalars is stable under
all scalars. This is the scalar-extension step for local tangent spaces. -/

open Set _root_.Topology

theorem closed_submodule_stable_under_dense_scalars
    {κ K A E : Type*} [Semiring κ] [Semiring K] [AddCommMonoid E]
    [Module κ E] [Module K E] [TopologicalSpace K] [TopologicalSpace E]
    [ContinuousSMul K E]
    (W : Submodule κ E) (hc : IsClosed (W : Set E))
    (f : A → K) (hd : DenseRange f)
    (hf : ∀ a : A, ∀ x ∈ W, f a • x ∈ W) :
    ∀ a : K, ∀ x ∈ W, a • x ∈ W := by
  intro a x hx
  have hpre : IsClosed {a : K | a • x ∈ W} := hc.preimage (continuous_id.smul continuous_const)
  apply closure_minimal _ hpre (hd a)
  rintro _ ⟨b, rfl⟩
  exact hf b x hx

def submoduleOverDenseScalars
    {κ K A E : Type*} [Semiring κ] [Semiring K] [AddCommMonoid E]
    [Module κ E] [Module K E] [TopologicalSpace K] [TopologicalSpace E]
    [ContinuousSMul K E]
    (W : Submodule κ E) (hc : IsClosed (W : Set E))
    (f : A → K) (hd : DenseRange f)
    (hf : ∀ a : A, ∀ x ∈ W, f a • x ∈ W) : Submodule K E where
  carrier := W
  zero_mem' := W.zero_mem
  add_mem' := W.add_mem
  smul_mem' := closed_submodule_stable_under_dense_scalars W hc f hd hf

@[simp] theorem submoduleOverDenseScalars_coe
    {κ K A E : Type*} [Semiring κ] [Semiring K] [AddCommMonoid E]
    [Module κ E] [Module K E] [TopologicalSpace K] [TopologicalSpace E]
    [ContinuousSMul K E]
    (W : Submodule κ E) (hc : IsClosed (W : Set E))
    (f : A → K) (hd : DenseRange f)
    (hf : ∀ a : A, ∀ x ∈ W, f a • x ∈ W) :
    (submoduleOverDenseScalars W hc f hd hf : Set E) = (W : Set E) := rfl

end

section

/-! The tangent commutator limit with a separate scalar field. This keeps
the prime-local-field dimension available in the closed-subgroup argument. -/

open scoped Classical
open Set Filter _root_.Topology

variable {F K κ : Type} [Field F] [Field K] [Field κ] [Algebra κ K]
variable [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)

theorem scaled_conjugation_displacement_over (g : G.Points ι)
    (X : Matrix (Fin n) (Fin n) K) (c : κ) :
    c • (TangentCone.matrixConjugation G ι g X - X) =
      ((c • ((g.val : Matrix (Fin n) (Fin n) K) - 1)) * X -
        X * (c • ((g.val : Matrix (Fin n) (Fin n) K) - 1))) *
          ((g⁻¹).val : Matrix (Fin n) (Fin n) K) := by
  simpa only [IsScalarTower.algebraMap_smul] using
    scaled_conjugation_displacement G ι g X (algebraMap κ K c)

theorem tangent_commutator_mem_over_of_conjugation_invariant
    (H : Subgroup (G.Points ι)) (W : Submodule κ (Matrix (Fin n) (Fin n) K))
    (hclosed : IsClosed (W : Set (Matrix (Fin n) (Fin n) K)))
    (hinvariant : ∀ g ∈ H, MapsTo (TangentCone.matrixConjugation G ι g)
      (W : Set (Matrix (Fin n) (Fin n) K)) (W : Set (Matrix (Fin n) (Fin n) K)))
    {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ W) (hY : Y ∈ matrixTangentConeOver (κ := κ) G ι H) :
    Y * X - X * Y ∈ W := by
  obtain ⟨α, l, hl, c, d, hd, hs, hcd⟩ := exists_fun_of_mem_tangentConeAt hY
  have hM : Tendsto (fun a => (1 : Matrix (Fin n) (Fin n) K) + d a) l (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hd
  have hi : Tendsto (fun a => ((1 : Matrix (Fin n) (Fin n) K) + d a).adjugate) l (𝓝 1) := by
    simpa only [Matrix.adjugate_one, Function.comp_def, id_eq] using
      (continuous_id.matrix_adjugate.tendsto 1).comp hM
  let z := fun a => ((c a • d a) * X - X * (c a • d a)) * (1 + d a).adjugate
  have hz : Tendsto z l (𝓝 (Y * X - X * Y)) := by
    simpa only [Matrix.mul_one] using
      ((hcd.mul tendsto_const_nhds).sub (tendsto_const_nhds.mul hcd)).mul hi
  apply hclosed.mem_of_tendsto hz
  filter_upwards [hs] with a ha
  obtain ⟨g, hg, hge⟩ := ha
  change (g.val : Matrix (Fin n) (Fin n) K) = 1 + d a at hge
  have hm := W.smul_mem (c a) (W.sub_mem (hinvariant g hg hX) hX)
  rw [scaled_conjugation_displacement_over] at hm
  have hginv : ((g⁻¹).val : Matrix (Fin n) (Fin n) K) = (1 + d a).adjugate := by
    calc
      _ = (g.val : Matrix (Fin n) (Fin n) K).adjugate := rfl
      _ = _ := congrArg Matrix.adjugate hge
  have hdg : (g.val : Matrix (Fin n) (Fin n) K) - 1 = d a := by
    simpa only [add_sub_cancel_left] using
      congrArg (fun M : Matrix (Fin n) (Fin n) K => M - 1) hge
  change z a ∈ W
  dsimp only [z]
  simpa only [hdg, hginv] using hm

end

/-! The closed prime subfield of a finite completion. Using this actual
closed subfield retains the smaller local scalar field without choosing
an identification with a particular model of the p-adic numbers. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

def closedPrimeSubfield (K : Type*) [NormedField K] : Subfield K :=
  (⊥ : Subfield K).topologicalClosure

instance closedPrimeSubfieldComplete (K : Type*) [NormedField K] [CompleteSpace K] :
    CompleteSpace (closedPrimeSubfield K) :=
  (⊥ : Subfield K).isClosed_topologicalClosure.completeSpace_coe

instance closedPrimeSubfieldNormedAlgebra (K : Type*) [NormedField K] :
    NormedAlgebra (closedPrimeSubfield K) K where
  norm_smul_le a x := norm_mul_le (a : K) x

variable {F : Type} [Field F] [NumberField F]

theorem exists_nat_norm_lt_one_at_finite_place (v : HeightOneSpectrum (𝓞 F)) :
    ∃ m : ℕ, 0 < m ∧ ‖(m : v.adicCompletion F)‖ < 1 := by
  let m := ringChar ((𝓞 F) ⧸ v.asIdeal)
  have hm : m ≠ 0 := CharP.ringChar_ne_zero_of_finite ((𝓞 F) ⧸ v.asIdeal)
  refine ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
  have hmI : (m : 𝓞 F) ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_natCast] using CharP.cast_eq_zero ((𝓞 F) ⧸ v.asIdeal) m
  apply Valued.toNormedField.norm_lt_one_iff.mpr
  rw [← map_natCast (algebraMap F (v.adicCompletion F))]
  change Valued.v ((m : F) : v.adicCompletion F) < 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hv := (HeightOneSpectrum.intValuation_lt_one_iff_mem v (m : 𝓞 F)).mpr hmI
  rw [← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap]
  exact hv

@[instance_reducible]
def finiteClosedPrimeNontriviallyNormedField (v : HeightOneSpectrum (𝓞 F)) :
    NontriviallyNormedField (closedPrimeSubfield (v.adicCompletion F)) where
  toNormedField := inferInstance
  non_trivial := by
      let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
      obtain ⟨m, hm, hnorm⟩ := exists_nat_norm_lt_one_at_finite_place v
      have hm0 : (m : closedPrimeSubfield (v.adicCompletion F)) ≠ 0 :=
        Nat.cast_ne_zero.mpr hm.ne'
      refine ⟨(m : closedPrimeSubfield (v.adicCompletion F))⁻¹, ?_⟩
      rw [norm_inv]
      apply (one_lt_inv₀ (norm_pos_iff.mpr hm0)).mpr
      exact hnorm

end

end OAI.NumberTheory.Quaternion.Arithmetic.TangentBracket
