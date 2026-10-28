import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

/-! # Spherical GU -/

namespace OAI.RepresentationTheory.Theta.Geometric.SphericalGU.Spherical

noncomputable section

/-!
# Concrete local Hecke objects for GeometricTheta

The spherical algebra is the endomorphism algebra of the compactly induced
trivial representation: equivariant endomorphisms of finitely supported
functions on G/K. This fixes multiplication as composition and the level
normalization as the delta function at K. No convolution compatibility or
geometric action is a field of this construction. We use inverse left-coset
coordinates, so gK corresponds to the manuscript's Kg⁻¹.
-/

variable {G : Type*} [Group G]

/-- Reuse TateComparison's actual rational convolution model. -/
abbrev CosetModule (K : Subgroup G) := AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.CosetModule K
abbrev algebra (K : Subgroup G) := AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.sphericalAlgebra K
abbrev kernel (K : Subgroup G) := AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel K

def coefficient (K : Subgroup G) (T : algebra K) (g : G) : ℚ :=
  kernel K T (QuotientGroup.mk g)

/-- The finite summation formula for the Weil action. On K-fixed inputs,
the value is independent of the chosen coset representatives. -/
def weilOperator {S : Type*} [AddCommGroup S] [Module ℂ S]
    (K : Subgroup G) (rho : G →* (S ≃ₗ[ℂ] S))
    (T : algebra K) : S →ₗ[ℂ] S :=
  (kernel K T).sum fun c a => (a : ℂ) • (rho c.out).toLinearMap

def fixedInputs {S : Type*} [AddCommGroup S] [Module ℂ S]
    (K : Subgroup G) (rho : G →* (S ≃ₗ[ℂ] S)) : Submodule ℂ S where
  carrier := {φ | ∀ k ∈ K, rho k φ = φ}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ k hk; simp [hφ k hk, hψ k hk]
  smul_mem' := by intro c φ hφ k hk; simp [hφ k hk]

/-- Changing a representative by an integral element does not change
its finite Weil transform on an integral-level fixed input. -/
theorem weil_value_eq_of_same_coset
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (K : Subgroup G) (rho : G →* (S ≃ₗ[ℂ] S))
    (φ : fixedInputs K rho) {g h : G}
    (heq : (QuotientGroup.mk g : G ⧸ K) = QuotientGroup.mk h) :
    rho g φ.val = rho h φ.val := by
  have hmem : g⁻¹ * h ∈ K := QuotientGroup.eq.mp heq
  have hfix := φ.property (g⁻¹ * h) hmem
  have h := congrArg (rho g) hfix
  simpa only [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left] using h.symm

section Weil

variable {S : Type*} [AddCommGroup S] [Module ℂ S]
  (K : Subgroup G) (rho : G →* (S ≃ₗ[ℂ] S))

def cosetValue (φ : fixedInputs K rho) : G ⧸ K → S :=
  Quotient.lift (fun g => rho g φ.val) (fun _ _ h =>
    weil_value_eq_of_same_coset K rho φ (Quotient.sound h))

@[simp] theorem cosetValue_mk (φ : fixedInputs K rho) (g : G) :
    cosetValue K rho φ (QuotientGroup.mk g) = rho g φ.val := rfl

theorem cosetValue_smul (φ : fixedInputs K rho) (g : G) (c : G ⧸ K) :
    cosetValue K rho φ (g • c) = rho g (cosetValue K rho φ c) := by
  induction c using Quotient.inductionOn with
  | h x =>
    change rho (g * x) φ.val = rho g (rho x φ.val)
    rw [map_mul, LinearEquiv.mul_apply]

variable [Module ℚ S] [IsScalarTower ℚ ℂ S]

def evaluateKernel (φ : fixedInputs K rho) : CosetModule K →ₗ[ℚ] S :=
  Finsupp.linearCombination ℚ (cosetValue K rho φ)

theorem evaluateKernel_translate (φ : fixedInputs K rho) (g : G) (v : CosetModule K) :
    evaluateKernel K rho φ (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g v) =
      rho g (evaluateKernel K rho φ v) := by
  have heq : (evaluateKernel K rho φ).comp (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g) =
      ((rho g).toLinearMap.restrictScalars ℚ).comp (evaluateKernel K rho φ) := by
    apply Finsupp.lhom_ext
    intro c r
    simp [evaluateKernel, cosetValue_smul]
    exact (((rho g).toLinearMap.restrictScalars ℚ).map_smul r _).symm
  exact LinearMap.congr_fun heq v

theorem kernel_fixed (T : algebra K) (k : G) (hk : k ∈ K) :
    AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K k (kernel K T) = kernel K T := by
  rw [← AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.hecke_single]
  have heq : (QuotientGroup.mk k : G ⧸ K) = QuotientGroup.mk 1 :=
    QuotientGroup.eq.mpr (by simpa using K.inv_mem hk)
  rw [heq]
  rfl

theorem weilOperator_eq_evaluateKernel (T : algebra K) (φ : fixedInputs K rho) :
    weilOperator K rho T φ.val = evaluateKernel K rho φ (kernel K T) := by
  change ((kernel K T).sum fun c a => (a : ℂ) • (rho c.out).toLinearMap) φ.val = _
  rw [LinearMap.finsupp_sum_apply]
  change (kernel K T).sum (fun c a => (a : ℂ) • rho c.out φ.val) =
    (kernel K T).sum (fun c a => a • cosetValue K rho φ c)
  apply Finsupp.sum_congr
  intro c hc
  have hv : cosetValue K rho φ c = rho c.out φ.val := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  rw [hv]
  exact IsScalarTower.algebraMap_smul ℂ (kernel K T c) (rho c.out φ.val)

theorem weilOperator_preserves_fixed (T : algebra K) (φ : fixedInputs K rho) :
    weilOperator K rho T φ.val ∈ fixedInputs K rho := by
  intro k hk
  rw [weilOperator_eq_evaluateKernel, ← evaluateKernel_translate, kernel_fixed K T k hk]

/-- The finite Weil spherical operator on integral-level fixed vectors,
constructed by the actual finite coset sum. -/
def weilAction (T : algebra K) : fixedInputs K rho →ₗ[ℂ] fixedInputs K rho :=
  LinearMap.codRestrict _ ((weilOperator K rho T).comp (fixedInputs K rho).subtype)
    (weilOperator_preserves_fixed K rho T)

end Weil

variable (q : ℕ) [Fact q.Prime]

abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]
abbrev GL3 := Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]

def integralSL3 : Subgroup (SL3 q) :=
  (Matrix.SpecialLinearGroup.map (PadicInt.Coe.ringHom (p := q))).range

def integralGL3 : Subgroup (GL3 q) :=
  (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q))).range

abbrev SL3Hecke := algebra (integralSL3 q)

/-- The completely split rational similitude group has one multiplier. -/
abbrev SplitGU (s : ℕ) := AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.SplitGroup s q

abbrev integralSplitGU (s : ℕ) := AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.integralLevel s q
abbrev FullHecke (s : ℕ) := AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q

/-- Trivial multiplier, one special-linear active block, identity elsewhere. -/
def activeEmbedding {s : ℕ} (active : Fin s) : SL3 q →* SplitGU q s where
  toFun g := (fun v => if v = active then Matrix.SpecialLinearGroup.toGL g else 1, 1)
  map_one' := by ext v <;> simp
  map_mul' g h := by
    apply Prod.ext
    · funext v
      change (if v = active then Matrix.SpecialLinearGroup.toGL (g * h) else 1) =
        (if v = active then Matrix.SpecialLinearGroup.toGL g else 1) *
          (if v = active then Matrix.SpecialLinearGroup.toGL h else 1)
      split_ifs <;> simp
    · simp

/-- Generated by the integral level and the determinant-one active block.
ElementaryDivisors identifies this with the zero active determinant-exponent sector. -/
def activeSector {s : ℕ} (active : Fin s) : Subgroup (SplitGU q s) :=
  integralSplitGU q s ⊔ (activeEmbedding q active).range

def activeOrbit {s : ℕ} (active : Fin s) : Set (SplitGU q s ⧸ integralSplitGU q s) :=
  QuotientGroup.mk '' (activeSector q active : Set (SplitGU q s))

def activeCosetModule {s : ℕ} (active : Fin s) :
    Submodule ℚ (CosetModule (integralSplitGU q s)) :=
  Finsupp.supported ℚ ℚ (activeOrbit q active)

/-- The spherical operators supported on the active sector. Equivariance
identifies support of the identity column with preservation of this module. -/
def activeAlgebra {s : ℕ} (active : Fin s) : Subalgebra ℚ (FullHecke q s) where
  carrier := {T | ∀ v ∈ activeCosetModule q active,
    T.val v ∈ activeCosetModule q active}
  zero_mem' := by
    change ∀ v ∈ activeCosetModule q active, (0 : FullHecke q s).val v ∈ activeCosetModule q active
    intro v hv
    exact (activeCosetModule q active).zero_mem
  add_mem' := by
    intro T U hT hU v hv
    exact (activeCosetModule q active).add_mem (hT v hv) (hU v hv)
  one_mem' := by intro v hv; exact hv
  mul_mem' := by intro T U hT hU v hv; exact hT _ (hU v hv)
  algebraMap_mem' := by
    intro c v hv
    exact (activeCosetModule q active).smul_mem c hv

end

end OAI.RepresentationTheory.Theta.Geometric.SphericalGU.Spherical
