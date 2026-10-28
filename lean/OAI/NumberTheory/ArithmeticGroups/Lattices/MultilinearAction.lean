import OAI.NumberTheory.ArithmeticGroups.Lattices.MultilinearBasisCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateRepresentation

/-! # Multilinear Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MultilinearAction.Construction

noncomputable section

section

/-! Contravariant actions on multilinear forms, expressed in their finite
basis-evaluation coordinates. -/

open scoped Classical

def multilinearContravariantRepresentation
    {R E A H : Type*} [Field R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] [Group H] (ρ : H →* (E ≃ₗ[R] E)) (r : ℕ) :
    H →* (MultilinearMap R (fun _ : Fin r => E) A ≃ₗ[R] MultilinearMap R (fun _ : Fin r => E) A) where
  toFun g := LinearEquiv.multilinearMapCongrLeft (fun _ : Fin r => ρ g⁻¹)
  map_one' := by
    apply LinearEquiv.ext
    intro f
    apply MultilinearMap.ext
    intro v
    change f (fun i => ρ (1 : H)⁻¹ (v i)) = f v
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro f
    apply MultilinearMap.ext
    intro v
    change f (fun i => ρ (g * h)⁻¹ (v i)) = f (fun i => ρ h⁻¹ (ρ g⁻¹ (v i)))
    rw [mul_inv_rev, map_mul]
    rfl

def multilinearBasisRepresentation
    {R E A H I : Type*} [Field R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] [Group H]
    (ρ : H →* (E ≃ₗ[R] E)) (b : Module.Basis I R E) (r : ℕ) :
    H →* ((MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range ≃ₗ[R]
      (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range) :=
  CoordinateRepresentation.Construction.transportLinearRepresentation (multilinearContravariantRepresentation (A := A) ρ r)
    (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r)

theorem multilinearBasisEvaluationEquiv_symm_evaluate
    {R E A I : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] (b : Module.Basis I R E) (r : ℕ)
    (x : (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range) (t : Fin r → I) :
    (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r).symm x (fun i => b (t i)) = x.val t :=
  congrArg (fun z : (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range => z.val t)
    ((MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r).apply_symm_apply x)

theorem multilinearBasisRepresentation_apply
    {R E A H I : Type*} [Field R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] [Group H] [Fintype I]
    (ρ : H →* (E ≃ₗ[R] E)) (b : Module.Basis I R E) (r : ℕ) (g : H)
    (x : (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range) (t : Fin r → I) :
    (multilinearBasisRepresentation ρ b r g x).val t =
      ∑ s : Fin r → I, (∏ i, b.repr (ρ g⁻¹ (b (t i))) (s i)) • x.val s := by
  change (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r).symm x (fun i => ρ g⁻¹ (b (t i))) = _
  rw [MultilinearBasisCoordinates.Construction.multilinear_basis_expansion b r]
  simp_rw [multilinearBasisEvaluationEquiv_symm_evaluate]

theorem continuous_multilinearBasisRepresentation
    {E A H I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Fintype I] (ρ : H →* (E ≃ₗ[ℝ] E)) (b : Module.Basis I ℝ E) (r : ℕ)
    (hρ : Continuous (fun a : H × E => ρ a.1 a.2)) :
    Continuous (fun a : H × (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range =>
      multilinearBasisRepresentation ρ b r a.1 a.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro t
  change Continuous (fun a : H × (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range =>
    (multilinearBasisRepresentation ρ b r a.1 a.2).val t)
  simp_rw [multilinearBasisRepresentation_apply]
  apply continuous_finsetSum
  intro s _
  apply Continuous.smul
  · apply continuous_finsetProd
    intro i _
    exact (b.coord (s i)).continuous_of_finiteDimensional.comp
      (hρ.comp ((continuous_inv.comp continuous_fst).prodMk continuous_const))
  · exact (continuous_apply s).comp (continuous_subtype_val.comp continuous_snd)

end

section

/-! Integer-valued multilinear forms form a closed discrete module in
finite basis coordinates. Lattice-preserving actions preserve it. -/

open scoped Classical

def integralMultilinearCoordinates
    {E A I : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A]
    (b : Module.Basis I ℝ E) (r : ℕ) (Ω : Submodule ℤ A) :
    Submodule ℤ (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range :=
  (Submodule.pi Set.univ (fun _ : Fin r → I => Ω)).comap
    ((MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range.subtype.restrictScalars ℤ)

theorem mem_integralMultilinearCoordinates
    {E A I : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A]
    (b : Module.Basis I ℝ E) (r : ℕ) (Ω : Submodule ℤ A)
    (x : (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range) :
    x ∈ integralMultilinearCoordinates b r Ω ↔ ∀ t, x.val t ∈ Ω := by
  change (∀ t ∈ Set.univ, x.val t ∈ Ω) ↔ _
  simp only [Set.mem_univ, forall_const]

theorem integralMultilinearCoordinates_discrete
    {E A I : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [Finite I]
    (b : Module.Basis I ℝ E) (r : ℕ) (Ω : Submodule ℤ A) [DiscreteTopology Ω] :
    DiscreteTopology (integralMultilinearCoordinates b r Ω) := by
  let f : integralMultilinearCoordinates b r Ω → ((Fin r → I) → Ω) := fun x t =>
    ⟨x.val.val t, (mem_integralMultilinearCoordinates b r Ω x.val).mp x.property t⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply continuous_pi
    intro t
    exact ((continuous_apply t).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  · intro x y he
    apply Subtype.ext
    apply Subtype.ext
    funext t
    exact congrArg (fun z : (Fin r → I) → Ω => (z t).val) he

theorem integralMultilinearCoordinates_closed
    {E A I : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [Finite I]
    (b : Module.Basis I ℝ E) (r : ℕ) (Ω : Submodule ℤ A) [DiscreteTopology Ω] :
    IsClosed (integralMultilinearCoordinates b r Ω :
      Set (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range) := by
  let : DiscreteTopology (integralMultilinearCoordinates b r Ω) :=
    integralMultilinearCoordinates_discrete b r Ω
  exact (integralMultilinearCoordinates b r Ω).toAddSubgroup.isClosed_of_discreteTopology

theorem integralMultilinearCoordinates_evaluate
    {E A I : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A]
    [Fintype I] (b : Module.Basis I ℝ E) (r : ℕ) (Ω : Submodule ℤ A)
    (x : (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range)
    (hx : x ∈ integralMultilinearCoordinates b r Ω) (v : Fin r → E)
    (hv : ∀ i, v i ∈ Submodule.span ℤ (Set.range b)) :
    (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r).symm x v ∈ Ω := by
  rw [MultilinearBasisCoordinates.Construction.multilinear_basis_expansion b r]
  apply Submodule.sum_mem
  intro t _
  rw [multilinearBasisEvaluationEquiv_symm_evaluate]
  have hi (i : Fin r) : ∃ z : ℤ, algebraMap ℤ ℝ z = b.repr (v i) (t i) :=
    (b.mem_span_iff_repr_mem ℤ (v i)).mp (hv i) (t i)
  choose z hz using hi
  have hc : (∏ i, b.repr (v i) (t i)) = algebraMap ℤ ℝ (∏ i, z i) := by
    simp only [map_prod, hz]
  rw [hc, IsScalarTower.algebraMap_smul]
  exact Ω.smul_mem _ ((mem_integralMultilinearCoordinates b r Ω x).mp hx t)

theorem integralMultilinearCoordinates_stable
    {E A H I : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A]
    [Group H] [Fintype I] (ρ : H →* (E ≃ₗ[ℝ] E)) (b : Module.Basis I ℝ E)
    (r : ℕ) (Ω : Submodule ℤ A) (Γ : Subgroup H)
    (hΓ : ∀ g ∈ Γ, ∀ v ∈ Submodule.span ℤ (Set.range b),
      ρ g v ∈ Submodule.span ℤ (Set.range b))
    {g : H} (hg : g ∈ Γ) {x : (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range}
    (hx : x ∈ integralMultilinearCoordinates b r Ω) :
    multilinearBasisRepresentation ρ b r g x ∈ integralMultilinearCoordinates b r Ω := by
  apply (mem_integralMultilinearCoordinates b r Ω _).mpr
  intro t
  change (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r).symm x (fun i => ρ g⁻¹ (b (t i))) ∈ Ω
  apply integralMultilinearCoordinates_evaluate b r Ω x hx
  intro i
  exact hΓ g⁻¹ (Γ.inv_mem hg) (b (t i)) (Submodule.subset_span (Set.mem_range_self (t i)))

end

/-! Tensor actions allowing simultaneous change of input and output
coordinates. Unary tensors include conjugation of endomorphisms. -/

open scoped Classical

def multilinearCovariantRepresentation
    {R E A H : Type*} [Field R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] [Group H]
    (ρ : H →* (E ≃ₗ[R] E)) (τ : H →* (A ≃ₗ[R] A)) (r : ℕ) :
    H →* (MultilinearMap R (fun _ : Fin r => E) A ≃ₗ[R] MultilinearMap R (fun _ : Fin r => E) A) where
  toFun g := (LinearEquiv.multilinearMapCongrLeft (fun _ : Fin r => ρ g⁻¹)).trans
    ((τ g).multilinearMapCongrRight R)
  map_one' := by
    apply LinearEquiv.ext
    intro f
    apply MultilinearMap.ext
    intro v
    change τ 1 (f (fun i => ρ (1 : H)⁻¹ (v i))) = f v
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro f
    apply MultilinearMap.ext
    intro v
    change τ (g * h) (f (fun i => ρ (g * h)⁻¹ (v i))) =
      τ g (τ h (f (fun i => ρ h⁻¹ (ρ g⁻¹ (v i)))))
    rw [mul_inv_rev, map_mul, map_mul]
    rfl

def multilinearCovariantBasisRepresentation
    {R E A H I : Type*} [Field R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] [Group H]
    (ρ : H →* (E ≃ₗ[R] E)) (τ : H →* (A ≃ₗ[R] A)) (b : Module.Basis I R E) (r : ℕ) :
    H →* ((MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range ≃ₗ[R]
      (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range) :=
  CoordinateRepresentation.Construction.transportLinearRepresentation (multilinearCovariantRepresentation ρ τ r)
    (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r)

theorem multilinearCovariantBasisRepresentation_apply
    {R E A H I : Type*} [Field R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] [Group H] [Fintype I]
    (ρ : H →* (E ≃ₗ[R] E)) (τ : H →* (A ≃ₗ[R] A)) (b : Module.Basis I R E) (r : ℕ) (g : H)
    (x : (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range) (t : Fin r → I) :
    (multilinearCovariantBasisRepresentation ρ τ b r g x).val t =
      ∑ s : Fin r → I, (∏ i, b.repr (ρ g⁻¹ (b (t i))) (s i)) • τ g (x.val s) := by
  change τ g ((MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r).symm x (fun i => ρ g⁻¹ (b (t i)))) = _
  rw [MultilinearBasisCoordinates.Construction.multilinear_basis_expansion b r, map_sum]
  simp_rw [multilinearBasisEvaluationEquiv_symm_evaluate, map_smul]

theorem continuous_multilinearCovariantBasisRepresentation
    {E A H I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Fintype I] (ρ : H →* (E ≃ₗ[ℝ] E)) (τ : H →* (A ≃ₗ[ℝ] A))
    (b : Module.Basis I ℝ E) (r : ℕ)
    (hρ : Continuous (fun a : H × E => ρ a.1 a.2))
    (hτ : Continuous (fun a : H × A => τ a.1 a.2)) :
    Continuous (fun a : H × (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range =>
      multilinearCovariantBasisRepresentation ρ τ b r a.1 a.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro t
  change Continuous (fun a : H × (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range =>
    (multilinearCovariantBasisRepresentation ρ τ b r a.1 a.2).val t)
  simp_rw [multilinearCovariantBasisRepresentation_apply]
  apply continuous_finsetSum
  intro s _
  apply Continuous.smul
  · apply continuous_finsetProd
    intro i _
    exact (b.coord (s i)).continuous_of_finiteDimensional.comp
      (hρ.comp ((continuous_inv.comp continuous_fst).prodMk continuous_const))
  · exact hτ.comp (continuous_fst.prodMk
      ((continuous_apply s).comp (continuous_subtype_val.comp continuous_snd)))

theorem integralMultilinearCoordinates_covariant_stable
    {E A H I : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A]
    [Group H] [Fintype I] (ρ : H →* (E ≃ₗ[ℝ] E)) (τ : H →* (A ≃ₗ[ℝ] A))
    (b : Module.Basis I ℝ E) (r : ℕ) (Ω : Submodule ℤ A) (Γ : Subgroup H)
    (hΓ : ∀ g ∈ Γ, ∀ v ∈ Submodule.span ℤ (Set.range b),
      ρ g v ∈ Submodule.span ℤ (Set.range b))
    (hΩ : ∀ g ∈ Γ, ∀ a ∈ Ω, τ g a ∈ Ω)
    {g : H} (hg : g ∈ Γ) {x : (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b r).range}
    (hx : x ∈ integralMultilinearCoordinates b r Ω) :
    multilinearCovariantBasisRepresentation ρ τ b r g x ∈ integralMultilinearCoordinates b r Ω := by
  apply (mem_integralMultilinearCoordinates b r Ω _).mpr
  intro t
  change τ g ((MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r).symm x (fun i => ρ g⁻¹ (b (t i)))) ∈ Ω
  apply hΩ g hg
  apply integralMultilinearCoordinates_evaluate b r Ω x hx
  intro i
  exact hΓ g⁻¹ (Γ.inv_mem hg) (b (t i)) (Submodule.subset_span (Set.mem_range_self (t i)))

theorem multilinearCovariantBasisRepresentation_fixed_iff
    {R E A H I : Type*} [Field R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] [Group H]
    (ρ : H →* (E ≃ₗ[R] E)) (τ : H →* (A ≃ₗ[R] A)) (b : Module.Basis I R E) (r : ℕ)
    (g : H) (f : MultilinearMap R (fun _ : Fin r => E) A) :
    multilinearCovariantBasisRepresentation ρ τ b r g (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r f) =
        MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r f ↔
      ∀ v, τ g (f (fun i => ρ g⁻¹ (v i))) = f v := by
  let e := MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv (A := A) b r
  change e (multilinearCovariantRepresentation ρ τ r g (e.symm (e f))) = e f ↔ _
  rw [e.symm_apply_apply, e.injective.eq_iff]
  exact ⟨fun h v => congrArg (fun F : MultilinearMap R (fun _ : Fin r => E) A => F v) h,
    fun h => MultilinearMap.ext h⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MultilinearAction.Construction
