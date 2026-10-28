import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Mem -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.Mem.Construction

noncomputable section

/-!
# Algebraic constructions for PeriodInvariants

This file constructs period invariants and their canonical scalar-extension map,
independently of any crystalline comparison theorem. In the intended application,
`R = ℚ_p`, `K0 = W(k)[1/p]`, `B = B_cris`, and `G = Gal(Kbar/K)`.

The geometric PeriodInvariants theorem is not yet established here. In particular, the
admissibility predicate below is a definition, never a hypothesis on all
cohomology representations or a field in a purported good-reduction model.
No statement stub is imported.
-/

open scoped TensorProduct

variable {R K0 B G V W U : Type*}
variable [CommRing R] [CommRing K0] [CommRing B]
variable [Algebra R K0] [Algebra R B] [Algebra K0 B]
variable [IsScalarTower R K0 B] [Group G]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]

/-- The diagonal Galois action on a period-ring tensor product. -/
def periodRepresentation (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) : Representation K0 G (B ⊗[R] V) where
  toFun g := TensorProduct.AlgebraTensorModule.map (σ g).toLinearMap (ρ g)
  map_one' := by
    ext b v
    simp
  map_mul' g h := by
    ext b v
    simp [Module.End.mul_apply]

@[simp]
theorem periodRepresentation_tmul (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) (g : G) (b : B) (v : V) :
    periodRepresentation σ ρ g (b ⊗ₜ[R] v) = σ g b ⊗ₜ[R] ρ g v := rfl

/-- The fixed subspace `(B ⊗[R] V)^G`, defined without comparison assumptions. -/
def periodInvariants (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) : Submodule K0 (B ⊗[R] V) :=
  (periodRepresentation σ ρ).invariants

@[simp]
theorem mem_periodInvariants (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) (x : B ⊗[R] V) :
    x ∈ periodInvariants σ ρ ↔ ∀ g, periodRepresentation σ ρ g x = x := Iff.rfl

/-- An equivariant map of representations stays equivariant after tensoring
with the period ring. -/
theorem periodMap_equivariant (σ : G →* B ≃ₐ[K0] B)
    {ρ : Representation R G V} {τ : Representation R G W}
    (f : Representation.IntertwiningMap ρ τ) (g : G) (x : B ⊗[R] V) :
    f.toLinearMap.baseChange B (periodRepresentation σ ρ g x) =
      periodRepresentation σ τ g (f.toLinearMap.baseChange B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b v => simp [f.isIntertwining]
  | add x y hx hy => simp [hx, hy]

/-- The map on period invariants induced by an equivariant linear map. -/
def periodMap (σ : G →* B ≃ₐ[K0] B)
    {ρ : Representation R G V} {τ : Representation R G W}
    (f : Representation.IntertwiningMap ρ τ) :
    periodInvariants σ ρ →ₗ[K0] periodInvariants σ τ :=
  ((f.toLinearMap.baseChange B).restrictScalars K0).restrict
    (fun x hx g => by
      change periodRepresentation σ τ g (f.toLinearMap.baseChange B x) =
        f.toLinearMap.baseChange B x
      rw [← periodMap_equivariant σ f g x]
      exact congrArg (f.toLinearMap.baseChange B) (hx g))

@[simp]
theorem periodMap_coe (σ : G →* B ≃ₐ[K0] B)
    {ρ : Representation R G V} {τ : Representation R G W}
    (f : Representation.IntertwiningMap ρ τ) (x : periodInvariants σ ρ) :
    (periodMap σ f x : B ⊗[R] W) = f.toLinearMap.baseChange B x := rfl

@[simp]
theorem periodMap_id (σ : G →* B ≃ₐ[K0] B) (ρ : Representation R G V) :
    periodMap σ (Representation.IntertwiningMap.id ρ) = LinearMap.id := by
  ext x
  simp

@[simp]
theorem periodMap_comp (σ : G →* B ≃ₐ[K0] B)
    {ρ : Representation R G V} {τ : Representation R G W}
    {υ : Representation R G U}
    (f : Representation.IntertwiningMap ρ τ)
    (g : Representation.IntertwiningMap τ υ) :
    periodMap σ (g.comp f) = (periodMap σ g).comp (periodMap σ f) := by
  ext x
  simp [LinearMap.baseChange_comp]

/-- The canonical multiplication map `B ⊗[K0] (B ⊗[R] V)^G → B ⊗[R] V`. -/
def periodComparisonMap (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) :
    B ⊗[K0] periodInvariants σ ρ →ₗ[B] B ⊗[R] V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b =>
        { toFun := fun x => b • (x : B ⊗[R] V)
          map_add' := by intros; simp [smul_add]
          map_smul' := fun c x => smul_comm b c (x : B ⊗[R] V) }
      map_add' := by intros; ext; simp [add_smul]
      map_smul' := by intros; ext; simp [smul_smul] }

@[simp]
theorem periodComparisonMap_tmul (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) (b : B) (x : periodInvariants σ ρ) :
    periodComparisonMap σ ρ (b ⊗ₜ[K0] x) = b • (x : B ⊗[R] V) := rfl

/-- Admissibility for a specified period ring is bijectivity of the canonical
map. Crystallinity is the specialization to Fontaine's actual `B_cris`. -/
def IsPeriodAdmissible (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) : Prop :=
  Function.Bijective (periodComparisonMap σ ρ)

/-- The canonical comparison map is natural for equivariant maps. -/
theorem periodComparisonMap_natural (σ : G →* B ≃ₐ[K0] B)
    {ρ : Representation R G V} {τ : Representation R G W}
    (f : Representation.IntertwiningMap ρ τ) :
    (f.toLinearMap.baseChange B).comp (periodComparisonMap σ ρ) =
      (periodComparisonMap σ τ).comp ((periodMap σ f).baseChange B) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  simp

section SemilinearOperator

/-- The period-ring operator viewed as semilinear over the coefficient field. -/
def scalarSemilinearOperator (F : K0 →+* K0) (φ : B →ₐ[R] B)
    (hφ : ∀ a c, φ (a • c) = F a • φ c) : B →ₛₗ[F] B where
  toFun := φ
  map_add' := φ.map_add
  map_smul' := hφ

/-- A period-ring operator acts on `B ⊗[R] V` and is semilinear over `K0`.
In the crystalline application this operator is Frobenius. -/
def periodOperator (F : K0 →+* K0) (φ : B →ₐ[R] B)
    (hφ : ∀ a c, φ (a • c) = F a • φ c) :
    B ⊗[R] V →ₛₗ[F] B ⊗[R] V where
  toFun := TensorProduct.map φ.toLinearMap LinearMap.id
  map_add' := (TensorProduct.map φ.toLinearMap LinearMap.id).map_add
  map_smul' a x := by
    induction x using TensorProduct.inductionOn with
    | tmul c v => simp [TensorProduct.smul_tmul', hφ]
    | add x y hx hy => simp [smul_add, hx, hy]

@[simp]
theorem periodOperator_tmul (F : K0 →+* K0) (φ : B →ₐ[R] B)
    (hφ : ∀ a c, φ (a • c) = F a • φ c) (c : B) (v : V) :
    periodOperator F φ hφ (c ⊗ₜ[R] v) = φ c ⊗ₜ[R] v := rfl

theorem periodOperator_equivariant (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) (F : K0 →+* K0) (φ : B →ₐ[R] B)
    (hφ : ∀ a c, φ (a • c) = F a • φ c)
    (hcomm : ∀ g c, φ (σ g c) = σ g (φ c)) (g : G) (x : B ⊗[R] V) :
    periodOperator F φ hφ (periodRepresentation σ ρ g x) =
      periodRepresentation σ ρ g (periodOperator F φ hφ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v => simp [hcomm]
  | add x y hx hy => simp [hx, hy]

/-- Frobenius restricts to period invariants because it commutes with Galois. -/
def periodInvariantOperator (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) (F : K0 →+* K0) (φ : B →ₐ[R] B)
    (hφ : ∀ a c, φ (a • c) = F a • φ c)
    (hcomm : ∀ g c, φ (σ g c) = σ g (φ c)) :
    periodInvariants σ ρ →ₛₗ[F] periodInvariants σ ρ :=
  (periodOperator F φ hφ).restrict (fun x hx g => by
    change periodRepresentation σ ρ g (periodOperator F φ hφ x) =
      periodOperator F φ hφ x
    rw [← periodOperator_equivariant σ ρ F φ hφ hcomm]
    exact congrArg (periodOperator F φ hφ) (hx g))

@[simp]
theorem periodInvariantOperator_coe (σ : G →* B ≃ₐ[K0] B)
    (ρ : Representation R G V) (F : K0 →+* K0) (φ : B →ₐ[R] B)
    (hφ : ∀ a c, φ (a • c) = F a • φ c)
    (hcomm : ∀ g c, φ (σ g c) = σ g (φ c)) (x : periodInvariants σ ρ) :
    (periodInvariantOperator σ ρ F φ hφ hcomm x : B ⊗[R] V) =
      periodOperator F φ hφ x := rfl

theorem periodOperator_natural (F : K0 →+* K0) (φ : B →ₐ[R] B)
    (hφ : ∀ a c, φ (a • c) = F a • φ c)
    (f : V →ₗ[R] W) (x : B ⊗[R] V) :
    periodOperator F φ hφ (f.baseChange B x) =
      f.baseChange B (periodOperator F φ hφ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v => simp
  | add x y hx hy => simp [hx, hy]

/-- Pullbacks induced by equivariant maps commute with the descended
semilinear period-ring operator. -/
theorem periodInvariantOperator_natural (σ : G →* B ≃ₐ[K0] B)
    {ρ : Representation R G V} {τ : Representation R G W}
    (F : K0 →+* K0) (φ : B →ₐ[R] B)
    (hφ : ∀ a c, φ (a • c) = F a • φ c)
    (hcomm : ∀ g c, φ (σ g c) = σ g (φ c))
    (f : Representation.IntertwiningMap ρ τ) (x : periodInvariants σ ρ) :
    periodInvariantOperator σ τ F φ hφ hcomm (periodMap σ f x) =
      periodMap σ f (periodInvariantOperator σ ρ F φ hφ hcomm x) := by
  apply Subtype.ext
  exact periodOperator_natural F φ hφ f.toLinearMap x

end SemilinearOperator

section InvariantEquivalence

variable {A X Y : Type*} [CommRing A]
variable [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]

/-- An equivariant linear equivalence restricts to the actual fixed subspaces. -/
def invariantEquiv {ρ : Representation A G X} {τ : Representation A G Y}
    (e : X ≃ₗ[A] Y) (he : ∀ g x, e (ρ g x) = τ g (e x)) :
    ρ.invariants ≃ₗ[A] τ.invariants where
  toFun x := ⟨e x, fun g => by rw [← he, x.property g]⟩
  invFun y := ⟨e.symm y, fun g => by
    apply e.injective
    rw [he, e.apply_symm_apply, y.property g]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add e (x : X) (y : X))
  map_smul' a x := Subtype.ext (map_smul e a (x : X))

@[simp]
theorem invariantEquiv_coe {ρ : Representation A G X} {τ : Representation A G Y}
    (e : X ≃ₗ[A] Y) (he : ∀ g x, e (ρ g x) = τ g (e x)) (x : ρ.invariants) :
    (invariantEquiv e he x : Y) = e x := rfl

end InvariantEquivalence

section FixedTensor

variable {K H ι : Type*} [Field K] [Algebra K B]
variable [AddCommGroup H] [Module K H]

/-- The map `h ↦ 1 ⊗ h` takes values in the fixed vectors when the action
on `H` is trivial. -/
def fixedTensorInclusion (σ : G →* B ≃ₐ[K] B) :
    H →ₗ[K] periodInvariants σ (Representation.trivial K G H) :=
  (TensorProduct.mk K B H 1).codRestrict _ (fun h g => by simp)

@[simp]
theorem fixedTensorInclusion_coe (σ : G →* B ≃ₐ[K] B) (h : H) :
    (fixedTensorInclusion σ h : B ⊗[K] H) = 1 ⊗ₜ[K] h := rfl

/-- For a trivial factor, the Galois action acts coefficientwise in a basis. -/
theorem fixedTensor_coefficient_action (σ : G →* B ≃ₐ[K] B)
    (b : Module.Basis ι K H) (g : G) (x : B ⊗[K] H) (i : ι) :
    (b.baseChange B).repr
        (periodRepresentation σ (Representation.trivial K G H) g x) i =
      σ g ((b.baseChange B).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul c h => simp [Module.Basis.baseChange_repr_tmul]
  | add x y hx hy => simp [hx, hy]

/-- If the fixed scalars in `B` are exactly `K`, every fixed tensor with a
finite-dimensional trivial factor comes from that factor. The fixed-scalar
condition is a separate input to this algebraic lemma, not a proved fact about
Fontaine's period ring. -/
theorem fixedTensorInclusion_bijective [Nontrivial B] [Fintype ι]
    (σ : G →* B ≃ₐ[K] B) (b : Module.Basis ι K H)
    (hfixed : ∀ c : B, (∀ g, σ g c = c) → ∃ a : K, algebraMap K B a = c) :
    Function.Bijective (fixedTensorInclusion σ (H := H)) := by
  classical
  constructor
  · intro h h' hh
    apply b.repr.injective
    ext i
    apply (algebraMap K B).injective
    have hi := congrArg (fun x : B ⊗[K] H => (b.baseChange B).repr x i)
      (congrArg Subtype.val hh)
    simpa [Module.Basis.baseChange_repr_tmul, Algebra.smul_def] using hi
  · intro x
    have hcoeff : ∀ i, ∃ a : K, algebraMap K B a = (b.baseChange B).repr x i := by
      intro i
      apply hfixed
      intro g
      rw [← fixedTensor_coefficient_action σ b g x i, x.property g]
    choose a ha using hcoeff
    refine ⟨∑ i, a i • b i, ?_⟩
    apply Subtype.ext
    apply (b.baseChange B).repr.injective
    ext i
    change (b.baseChange B).repr (1 ⊗ₜ[K] ∑ j, a j • b j) i = _
    rw [Module.Basis.baseChange_repr_tmul]
    simpa [map_sum, Algebra.smul_def, Finsupp.single_apply] using ha i

/-- Scalar descent for the trivial factor, obtained by proving bijectivity of
`h ↦ 1 ⊗ h`, rather than including an equivalence as data. -/
def fixedTensorEquiv [Nontrivial B] [Fintype ι]
    (σ : G →* B ≃ₐ[K] B) (b : Module.Basis ι K H)
    (hfixed : ∀ c : B, (∀ g, σ g c = c) → ∃ a : K, algebraMap K B a = c) :
    H ≃ₗ[K] periodInvariants σ (Representation.trivial K G H) :=
  LinearEquiv.ofBijective (fixedTensorInclusion σ)
    (fixedTensorInclusion_bijective σ b hfixed)

@[simp]
theorem fixedTensorEquiv_coe [Nontrivial B] [Fintype ι]
    (σ : G →* B ≃ₐ[K] B) (b : Module.Basis ι K H)
    (hfixed : ∀ c : B, (∀ g, σ g c = c) → ∃ a : K, algebraMap K B a = c)
    (h : H) :
    (fixedTensorEquiv σ b hfixed h : B ⊗[K] H) = 1 ⊗ₜ[K] h := rfl

end FixedTensor

variable {K H ι : Type*} [Field K] [Algebra R K] [Algebra K B]
variable [IsScalarTower R K B] [Nontrivial B]
variable [AddCommGroup H] [Module K H] [Fintype ι]

/-- Algebraic descent of an equivariant period-ring equivalence. The input
`e` is not supplied by this construction; obtaining it from smooth proper
geometry remains the crystalline comparison theorem. -/
def descentEquiv (σ : G →* B ≃ₐ[K] B) (ρ : Representation R G V)
    (b : Module.Basis ι K H)
    (hfixed : ∀ c : B, (∀ g, σ g c = c) → ∃ a : K, algebraMap K B a = c)
    (e : (B ⊗[R] V) ≃ₗ[B] (B ⊗[K] H))
    (he : ∀ g x, e (periodRepresentation σ ρ g x) =
      periodRepresentation σ (Representation.trivial K G H) g (e x)) :
    periodInvariants σ ρ ≃ₗ[K] H :=
  (invariantEquiv (e.restrictScalars K) he).trans (fixedTensorEquiv σ b hfixed).symm

theorem descentEquiv_spec (σ : G →* B ≃ₐ[K] B) (ρ : Representation R G V)
    (b : Module.Basis ι K H)
    (hfixed : ∀ c : B, (∀ g, σ g c = c) → ∃ a : K, algebraMap K B a = c)
    (e : (B ⊗[R] V) ≃ₗ[B] (B ⊗[K] H))
    (he : ∀ g x, e (periodRepresentation σ ρ g x) =
      periodRepresentation σ (Representation.trivial K G H) g (e x))
    (x : periodInvariants σ ρ) :
    e x = 1 ⊗ₜ[K] descentEquiv σ ρ b hfixed e he x := by
  have h := congrArg Subtype.val ((fixedTensorEquiv σ b hfixed).apply_symm_apply
    (invariantEquiv (e.restrictScalars K) he x))
  exact h.symm

/-- After descent, the canonical scalar-extension map agrees with the given
period-ring equivalence. This identification proves its bijectivity below. -/
theorem descentEquiv_baseChange (σ : G →* B ≃ₐ[K] B) (ρ : Representation R G V)
    (b : Module.Basis ι K H)
    (hfixed : ∀ c : B, (∀ g, σ g c = c) → ∃ a : K, algebraMap K B a = c)
    (e : (B ⊗[R] V) ≃ₗ[B] (B ⊗[K] H))
    (he : ∀ g x, e (periodRepresentation σ ρ g x) =
      periodRepresentation σ (Representation.trivial K G H) g (e x)) :
    e.toLinearMap.comp (periodComparisonMap σ ρ) =
      (descentEquiv σ ρ b hfixed e he).toLinearMap.baseChange B := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  change e (c • (x : B ⊗[R] V)) = c ⊗ₜ[K] descentEquiv σ ρ b hfixed e he x
  rw [map_smul, descentEquiv_spec σ ρ b hfixed e he]
  simp [TensorProduct.smul_tmul']

/-- Pure algebraic consequence of a period-ring comparison: its source
representation is admissible for that period ring. The geometric comparison
and the period ring's fixed-scalar theorem remain separate proof obligations. -/
theorem admissible_of_period_equiv (σ : G →* B ≃ₐ[K] B)
    (ρ : Representation R G V) (b : Module.Basis ι K H)
    (hfixed : ∀ c : B, (∀ g, σ g c = c) → ∃ a : K, algebraMap K B a = c)
    (e : (B ⊗[R] V) ≃ₗ[B] (B ⊗[K] H))
    (he : ∀ g x, e (periodRepresentation σ ρ g x) =
      periodRepresentation σ (Representation.trivial K G H) g (e x)) :
    IsPeriodAdmissible σ ρ := by
  have hcomp : Function.Bijective (e.toLinearMap.comp (periodComparisonMap σ ρ)) := by
    rw [descentEquiv_baseChange σ ρ b hfixed e he]
    exact ((descentEquiv σ ρ b hfixed e he).baseChange K B _ _).bijective
  constructor
  · intro x y h
    apply hcomp.injective
    exact congrArg e h
  · intro y
    obtain ⟨x, hx⟩ := hcomp.surjective (e y)
    exact ⟨x, e.injective hx⟩

/-- Endomorphism compatibility descends from the period-ring comparison. -/
theorem descentEquiv_natural (σ : G →* B ≃ₐ[K] B) (ρ : Representation R G V)
    (b : Module.Basis ι K H)
    (hfixed : ∀ c : B, (∀ g, σ g c = c) → ∃ a : K, algebraMap K B a = c)
    (e : (B ⊗[R] V) ≃ₗ[B] (B ⊗[K] H))
    (he : ∀ g x, e (periodRepresentation σ ρ g x) =
      periodRepresentation σ (Representation.trivial K G H) g (e x))
    (f : Representation.IntertwiningMap ρ ρ) (q : H →ₗ[K] H)
    (hnatural : ∀ x, e (f.toLinearMap.baseChange B x) = q.baseChange B (e x))
    (x : periodInvariants σ ρ) :
    descentEquiv σ ρ b hfixed e he (periodMap σ f x) =
      q (descentEquiv σ ρ b hfixed e he x) := by
  apply (fixedTensorEquiv σ b hfixed).injective
  apply Subtype.ext
  change 1 ⊗ₜ[K] descentEquiv σ ρ b hfixed e he (periodMap σ f x) =
    1 ⊗ₜ[K] q (descentEquiv σ ρ b hfixed e he x)
  rw [← descentEquiv_spec σ ρ b hfixed e he]
  change e (f.toLinearMap.baseChange B x) = _
  rw [hnatural, descentEquiv_spec σ ρ b hfixed e he]
  rfl

/-- Frobenius compatibility of a period-ring comparison descends to its
comparison on invariants. Both Frobenius operators retain their semilinearity. -/
theorem descentEquiv_frobenius (σ : G →* B ≃ₐ[K] B) (ρ : Representation R G V)
    (b : Module.Basis ι K H)
    (hfixed : ∀ c : B, (∀ g, σ g c = c) → ∃ a : K, algebraMap K B a = c)
    (e : (B ⊗[R] V) ≃ₗ[B] (B ⊗[K] H))
    (he : ∀ g x, e (periodRepresentation σ ρ g x) =
      periodRepresentation σ (Representation.trivial K G H) g (e x))
    (F : K →+* K) (φ : B →ₐ[R] B)
    (hφ : ∀ a c, φ (a • c) = F a • φ c)
    (hcomm : ∀ g c, φ (σ g c) = σ g (φ c))
    (ψ : H →ₛₗ[F] H)
    (heφ : ∀ x, e (periodOperator F φ hφ x) =
      TensorProduct.map (scalarSemilinearOperator F φ hφ) ψ (e x))
    (x : periodInvariants σ ρ) :
    descentEquiv σ ρ b hfixed e he (periodInvariantOperator σ ρ F φ hφ hcomm x) =
      ψ (descentEquiv σ ρ b hfixed e he x) := by
  apply (fixedTensorEquiv σ b hfixed).injective
  apply Subtype.ext
  change 1 ⊗ₜ[K] descentEquiv σ ρ b hfixed e he
      (periodInvariantOperator σ ρ F φ hφ hcomm x) =
    1 ⊗ₜ[K] ψ (descentEquiv σ ρ b hfixed e he x)
  rw [← descentEquiv_spec σ ρ b hfixed e he]
  change e (periodOperator F φ hφ x) = _
  rw [heφ, descentEquiv_spec σ ρ b hfixed e he]
  simp [scalarSemilinearOperator]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.Mem.Construction
