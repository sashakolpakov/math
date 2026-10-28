import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local

/-! # Hecke Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

noncomputable section

section

/-!
The spherical algebra is constructed as the algebra of equivariant
endomorphisms of the free rational module on G/K. Equivariance forces each
column to be a translate of the finite identity column. Thus this is the
ordinary finite-support convolution model, with integral-level volume one;
no convolution constants or geometric action are supplied as data.
-/

open scoped Classical

section Convolution

variable {G : Type*} [Group G] (U : Subgroup G)

/-- The free rational module on right cosets. Inversion identifies these
with the left-coset convention used for the inverse lattice representatives. -/
abbrev CosetModule := (G ⧸ U) →₀ ℚ

/-- The permutation representation on the coset module. -/
def translate (g : G) : Module.End ℚ (CosetModule U) :=
  Finsupp.lmapDomain ℚ ℚ (fun x : G ⧸ U => g • x)

@[simp]
theorem translate_single (g : G) (x : G ⧸ U) (r : ℚ) :
    translate U g (Finsupp.single x r) = Finsupp.single (g • x) r := by
  simp [translate]

theorem translate_mul (g h : G) : translate U (g * h) = translate U g * translate U h := by
  apply Finsupp.lhom_ext
  intro x r
  simp [Module.End.mul_apply, mul_smul]

@[simp]
theorem translate_one : translate U (1 : G) = 1 := by
  apply Finsupp.lhom_ext
  intro x r
  simp

/-- The genuine spherical convolution algebra, in its coset-module model. -/
def sphericalAlgebra : Subalgebra ℚ (Module.End ℚ (CosetModule U)) :=
  Subalgebra.centralizer ℚ (Set.range (translate U))

abbrev SphericalHecke := sphericalAlgebra U

/-- Equivariance follows from the definition of the algebra. -/
theorem hecke_translate (T : SphericalHecke U) (g : G) (v : CosetModule U) :
    T.val (translate U g v) = translate U g (T.val v) := by
  have h := T.property (translate U g) ⟨g, rfl⟩
  exact (LinearMap.congr_fun h v).symm

/-- The finite-support identity column is the convolution kernel. -/
def kernel (T : SphericalHecke U) : CosetModule U :=
  T.val (Finsupp.single (QuotientGroup.mk (1 : G)) 1)

/-- A matrix column is a translated identity column. -/
theorem hecke_single (T : SphericalHecke U) (g : G) :
    T.val (Finsupp.single (QuotientGroup.mk g) 1) =
      translate U g (kernel U T) := by
  have h := hecke_translate U T g
    (Finsupp.single (QuotientGroup.mk (1 : G)) 1)
  simpa [kernel, translate] using h

/-- No algebra element is hidden by the finite convolution-kernel model. -/
theorem kernel_injective : Function.Injective (kernel U) := by
  intro T S hTS
  apply Subtype.ext
  apply Finsupp.lhom_ext
  intro x r
  induction x using Quotient.inductionOn with
  | h g =>
    have h1 : T.val (Finsupp.single (QuotientGroup.mk g) 1) =
        S.val (Finsupp.single (QuotientGroup.mk g) 1) := by
      rw [hecke_single, hecke_single, hTS]
    have hr := congrArg (fun v : CosetModule U => r • v) h1
    simpa only [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one] using hr

/-- Multiplication is computed by applying one kernel operator to the other
finite kernel. This determines convolution, without an assumed multiplication law. -/
theorem kernel_mul (S T : SphericalHecke U) :
    kernel U (S * T) = S.val (kernel U T) := rfl

/-- Raw double cosets are unnormalized characteristic functions. The inverse
is the manuscript's superlattice convention. Existence is not assumed here. -/
def IsRawDoubleCoset (g : G) (T : SphericalHecke U) : Prop :=
  ∀ x : G,
    kernel U T (QuotientGroup.mk x) =
      if ∃ k l : U, x = (k : G) * g⁻¹ * (l : G) then 1 else 0

theorem rawDoubleCoset_unique {g : G} {S T : SphericalHecke U}
    (hS : IsRawDoubleCoset U g S) (hT : IsRawDoubleCoset U g T) : S = T := by
  apply kernel_injective U
  ext x
  induction x using Quotient.inductionOn with
  | h x => rw [hS x, hT x]

/-- A central group element gives an actual equivariant permutation operator. -/
def centralTranslation (z : G) (hz : ∀ g : G, Commute g z) : SphericalHecke U :=
  ⟨translate U z, by
    rintro _ ⟨g, rfl⟩
    rw [← translate_mul, ← translate_mul, (hz g).eq]⟩

/-- The central double coset is invertible, before any geometric action is
constructed. The inverse representative implements the superlattice convention. -/
def centralHeckeUnit (z : G) (hz : ∀ g : G, Commute g z) : (SphericalHecke U)ˣ where
  val := centralTranslation U z⁻¹ (fun g => (hz g).inv_right)
  inv := centralTranslation U z hz
  val_inv := by
    apply Subtype.ext
    change translate U z⁻¹ * translate U z = 1
    rw [← translate_mul, inv_mul_cancel, translate_one]
  inv_val := by
    apply Subtype.ext
    change translate U z * translate U z⁻¹ = 1
    rw [← translate_mul, mul_inv_cancel, translate_one]

theorem centralHeckeUnit_kernel (z : G) (hz : ∀ g : G, Commute g z) :
    kernel U (centralHeckeUnit U z hz).val =
      Finsupp.single (QuotientGroup.mk z⁻¹) 1 := by
  simp [kernel, centralHeckeUnit, centralTranslation, translate]

end Convolution

variable (s q : ℕ) [Fact q.Prime]

/-- The split local similitude group has one shared rational multiplier. -/
abbrev SplitGroup :=
  (Fin s → Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) × (ℚ_[q])ˣ

/-- Integral blocks and an integral unit multiplier embed in the split group. -/
def integralLevelMap :
    ((Fin s → Matrix.GeneralLinearGroup (Fin 3) ℤ_[q]) × (ℤ_[q])ˣ) →*
      HeckeKernel.SplitGroup s q where
  toFun x := (fun v => Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) (x.1 v),
    Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom x.2)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp

/-- The spherical integral-level subgroup. -/
def integralLevel : Subgroup (HeckeKernel.SplitGroup s q) := (integralLevelMap s q).range

/-- The rank-three spherical algebra used by TateComparison. -/
abbrev Hecke := SphericalHecke (integralLevel s q)

/-- q is a unit in Q_q, even though it is not a unit in Z_q. -/
def qUnit : (ℚ_[q])ˣ :=
  Units.mk0 (q : ℚ_[q]) (by exact_mod_cast (Fact.out : q.Prime).ne_zero)

/-- A diagonal matrix built from three units, with its inverse constructed. -/
def diagonalUnit {R : Type*} [CommRing R] (d : Fin 3 → Rˣ) :
    Matrix.GeneralLinearGroup (Fin 3) R where
  val := Matrix.diagonal (fun i => (d i : R))
  inv := Matrix.diagonal (fun i => ((d i)⁻¹ : Rˣ))
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

/-- The cocharacter representative has chosen-side powers and one multiplier. -/
def representative (t : Local.LocalType s) : HeckeKernel.SplitGroup s q :=
  (fun v => diagonalUnit (fun i => qUnit q ^ t.exponent v i),
    qUnit q ^ t.multiplier)

/-- The source's q²-multiplier central element. -/
def centralElement : HeckeKernel.SplitGroup s q :=
  (fun _ => Matrix.GeneralLinearGroup.scalar (Fin 3) (qUnit q), (qUnit q) ^ 2)

theorem centralElement_commutes (g : HeckeKernel.SplitGroup s q) : Commute g (centralElement s q) := by
  change g * centralElement s q = centralElement s q * g
  apply Prod.ext
  · funext v
    exact (Matrix.GeneralLinearGroup.scalar_commute (qUnit q) (g.1 v)).symm
  · exact mul_comm _ _

/-- A concrete invertible central operator in the spherical algebra. -/
def scalarHeckeUnit : (Hecke s q)ˣ :=
  centralHeckeUnit (integralLevel s q) (centralElement s q) (centralElement_commutes s q)

theorem representative_central :
    representative s q (Local.LocalType.central s) = centralElement s q := by
  apply Prod.ext
  · funext v
    apply Units.ext
    simp [representative, centralElement, diagonalUnit, Local.LocalType.central,
      Matrix.GeneralLinearGroup.scalar, Matrix.scalar]
  · simp [representative, centralElement, Local.LocalType.central]

end

section

/-!
Construction of an equivariant coset-module operator from its invariant
finite kernel. Raw operators are then obtained from finite subgroup orbits.
Neither multiplication nor equivariance is assumed of the constructed map.
-/

open scoped Classical

variable {G : Type*} [Group G] (U : Subgroup G)

def IsInvariantKernel (k : CosetModule U) : Prop :=
  ∀ u : U, translate U (u : G) k = k

/-- Translation of an invariant kernel is independent of the coset representative. -/
def kernelColumn (k : CosetModule U) (hk : IsInvariantKernel U k) :
    G ⧸ U → CosetModule U :=
  Quotient.lift (fun g => translate U g k) (by
    intro a b hab
    have hu : a⁻¹ * b ∈ U := QuotientGroup.leftRel_apply.mp hab
    have h := congrArg (fun v => translate U a v) (hk ⟨a⁻¹ * b, hu⟩)
    simpa only [← Module.End.mul_apply, ← translate_mul, mul_inv_cancel_left] using h.symm)

@[simp]
theorem kernelColumn_mk (k : CosetModule U) (hk : IsInvariantKernel U k) (g : G) :
    kernelColumn U k hk (QuotientGroup.mk g) = translate U g k := rfl

theorem kernelColumn_translate (k : CosetModule U) (hk : IsInvariantKernel U k)
    (g : G) (x : G ⧸ U) :
    kernelColumn U k hk (g • x) = translate U g (kernelColumn U k hk x) := by
  induction x using Quotient.inductionOn with
  | h x =>
    change translate U (g * x) k = translate U g (translate U x k)
    rw [translate_mul, Module.End.mul_apply]

/-- Linear extension of the translated columns. -/
def kernelOperator (k : CosetModule U) (hk : IsInvariantKernel U k) :
    Module.End ℚ (CosetModule U) :=
  Finsupp.linearCombination ℚ (kernelColumn U k hk)

@[simp]
theorem kernelOperator_single (k : CosetModule U) (hk : IsInvariantKernel U k)
    (x : G ⧸ U) (r : ℚ) :
    kernelOperator U k hk (Finsupp.single x r) = r • kernelColumn U k hk x :=
  Finsupp.linearCombination_single _ _ _

/-- The constructed operator commutes with all group translations. -/
def heckeOfKernel (k : CosetModule U) (hk : IsInvariantKernel U k) : SphericalHecke U :=
  ⟨kernelOperator U k hk, by
    rintro _ ⟨g, rfl⟩
    apply Finsupp.lhom_ext
    intro x r
    change translate U g (kernelOperator U k hk (Finsupp.single x r)) =
      kernelOperator U k hk (translate U g (Finsupp.single x r))
    rw [translate_single, kernelOperator_single, kernelOperator_single,
      kernelColumn_translate, map_smul]⟩

@[simp]
theorem kernel_heckeOfKernel (k : CosetModule U) (hk : IsInvariantKernel U k) :
    kernel U (heckeOfKernel U k hk) = k := by
  change kernelOperator U k hk (Finsupp.single (QuotientGroup.mk 1) 1) = k
  rw [kernelOperator_single, one_smul, kernelColumn_mk, translate_one]
  rfl

theorem kernel_invariant (T : SphericalHecke U) : IsInvariantKernel U (kernel U T) := by
  intro u
  rw [← hecke_single]
  have h : (QuotientGroup.mk (u : G) : G ⧸ U) = QuotientGroup.mk (1 : G) := by
    apply QuotientGroup.eq.mpr
    rw [mul_one]
    exact U.inv_mem u.property
  rw [h]
  rfl

/-- The kernel construction is inverse to extracting the identity column. -/
theorem heckeOfKernel_kernel (T : SphericalHecke U) :
    heckeOfKernel U (kernel U T) (kernel_invariant U T) = T :=
  kernel_injective U (kernel_heckeOfKernel U _ _)

/-- Evaluation of a translated coefficient at the translated coset. -/
theorem translate_apply_smul (g : G) (k : CosetModule U) (x : G ⧸ U) :
    translate U g k (g • x) = k x := by
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective g) k x

def doubleCosetOrbit (g : G) : Set (G ⧸ U) :=
  Set.range (fun u : U => (u : G) • QuotientGroup.mk g⁻¹)

theorem mem_doubleCosetOrbit (g x : G) :
    QuotientGroup.mk x ∈ doubleCosetOrbit U g ↔
      ∃ k l : U, x = (k : G) * g⁻¹ * (l : G) := by
  constructor
  · rintro ⟨k, hk⟩
    have hr : (k.val * g⁻¹)⁻¹ * x ∈ U := QuotientGroup.eq.mp hk
    refine ⟨k, ⟨(k.val * g⁻¹)⁻¹ * x, hr⟩, ?_⟩
    change x = (k.val * g⁻¹) * ((k.val * g⁻¹)⁻¹ * x)
    exact (mul_inv_cancel_left _ _).symm
  · rintro ⟨k, l, rfl⟩
    refine ⟨k, ?_⟩
    apply QuotientGroup.eq.mpr
    change (k.val * g⁻¹)⁻¹ * ((k.val * g⁻¹) * l.val) ∈ U
    simpa only [inv_mul_cancel_left] using l.property

theorem smul_mem_doubleCosetOrbit (g : G) (u : U) (x : G ⧸ U) :
    (u : G) • x ∈ doubleCosetOrbit U g ↔ x ∈ doubleCosetOrbit U g := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨u⁻¹ * v, ?_⟩
    have h := congrArg (fun z : G ⧸ U => (u.val)⁻¹ • z) hv
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul] using h
  · rintro ⟨v, rfl⟩
    exact ⟨u * v, mul_smul _ _ _⟩

/-- The unnormalized characteristic kernel of a finite double-coset orbit. -/
def rawKernel (g : G) (hg : (doubleCosetOrbit U g).Finite) : CosetModule U :=
  Finsupp.indicator hg.toFinset (fun _ _ => 1)

@[simp]
theorem rawKernel_apply (g : G) (hg : (doubleCosetOrbit U g).Finite) (x : G ⧸ U) :
    rawKernel U g hg x = if x ∈ doubleCosetOrbit U g then 1 else 0 := by
  simp [rawKernel, Finsupp.indicator_apply]

theorem rawKernel_invariant (g : G) (hg : (doubleCosetOrbit U g).Finite) :
    IsInvariantKernel U (rawKernel U g hg) := by
  intro u
  ext x
  obtain ⟨y, rfl⟩ := MulAction.surjective (u : G) x
  rw [translate_apply_smul, rawKernel_apply, rawKernel_apply,
    smul_mem_doubleCosetOrbit]

/-- A finite double coset gives the actual raw Hecke operator. -/
def rawHecke (g : G) (hg : (doubleCosetOrbit U g).Finite) : SphericalHecke U :=
  heckeOfKernel U (rawKernel U g hg) (rawKernel_invariant U g hg)

theorem rawHecke_isRaw (g : G) (hg : (doubleCosetOrbit U g).Finite) :
    IsRawDoubleCoset U g (rawHecke U g hg) := by
  intro x
  rw [rawHecke, kernel_heckeOfKernel, rawKernel_apply, mem_doubleCosetOrbit]

end

section

/-! Raw convolution has nonnegative integral coefficients. The statements
refer to the actual coset kernels; no multiplicity table is supplied. -/

open scoped Classical

variable {G : Type*} [Group G] (U : Subgroup G)

def kernelLinear : SphericalHecke U →ₗ[ℚ] CosetModule U where
  toFun := kernel U
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def NatValuedKernel (k : CosetModule U) : Prop := ∀ x, ∃ n : ℕ, k x = (n : ℚ)

theorem kernel_u_smul (T : SphericalHecke U) (u : U) (x : G ⧸ U) :
    kernel U T ((u : G) • x) = kernel U T x := by
  have h := congrArg (fun k : CosetModule U => k ((u : G) • x)) (kernel_invariant U T u)
  rw [translate_apply_smul] at h
  exact h.symm

theorem kernel_eq_of_same_orbit (T : SphericalHecke U) (g : G) {x y : G ⧸ U}
    (hx : x ∈ doubleCosetOrbit U g) (hy : y ∈ doubleCosetOrbit U g) :
    kernel U T x = kernel U T y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  rw [kernel_u_smul, kernel_u_smul]

theorem raw_kernel_at {g : G} {T : SphericalHecke U} (hT : IsRawDoubleCoset U g T)
    (x : G ⧸ U) : kernel U T x = if x ∈ doubleCosetOrbit U g then 1 else 0 := by
  induction x using Quotient.inductionOn with
  | h x => rw [hT, mem_doubleCosetOrbit]

theorem raw_natValued {g : G} {T : SphericalHecke U} (hT : IsRawDoubleCoset U g T) :
    NatValuedKernel U (kernel U T) := by
  intro x
  rw [raw_kernel_at U hT]
  split_ifs
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

theorem natValued_translate {k : CosetModule U} (hk : NatValuedKernel U k) (g : G) :
    NatValuedKernel U (translate U g k) := by
  intro x
  obtain ⟨y, rfl⟩ := MulAction.surjective g x
  rw [translate_apply_smul]
  exact hk y

theorem natValued_column {k : CosetModule U} (hk : NatValuedKernel U k)
    (hfix : IsInvariantKernel U k) (x : G ⧸ U) :
    NatValuedKernel U (kernelColumn U k hfix x) := by
  induction x using Quotient.inductionOn with
  | h x => exact natValued_translate U hk x

theorem kernelOperator_apply (k : CosetModule U) (hk : IsInvariantKernel U k)
    (f : CosetModule U) (x : G ⧸ U) :
    kernelOperator U k hk f x =
      ∑ y ∈ f.support, f y * kernelColumn U k hk y x := by
  simp only [kernelOperator, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem natValued_kernelOperator {k f : CosetModule U}
    (hk : NatValuedKernel U k) (hfix : IsInvariantKernel U k)
    (hf : NatValuedKernel U f) : NatValuedKernel U (kernelOperator U k hfix f) := by
  intro x
  choose n hn using hf
  choose m hm using fun y => natValued_column U hk hfix y x
  refine ⟨∑ y ∈ f.support, n y * m y, ?_⟩
  rw [kernelOperator_apply]
  simp only [hn, hm, Nat.cast_sum, Nat.cast_mul]

theorem natValued_kernel_mul (S T : SphericalHecke U)
    (hS : NatValuedKernel U (kernel U S)) (hT : NatValuedKernel U (kernel U T)) :
    NatValuedKernel U (kernel U (S * T)) := by
  have hSmap : S.val = kernelOperator U (kernel U S) (kernel_invariant U S) :=
    (congrArg Subtype.val (heckeOfKernel_kernel U S)).symm
  rw [kernel_mul, hSmap]
  exact natValued_kernelOperator U hS _ hT

/-- Subtracting one complete raw orbit removes that orbit and leaves
every other coefficient unchanged. -/
theorem kernel_sub_raw_apply (S T : SphericalHecke U) {g : G}
    (hT : IsRawDoubleCoset U g T) {x : G ⧸ U} (hx : x ∈ doubleCosetOrbit U g)
    (n : ℕ) (hn : kernel U S x = (n : ℚ)) (y : G ⧸ U) :
    kernel U (S - n • T) y =
      if y ∈ doubleCosetOrbit U g then 0 else kernel U S y := by
  have hlin : kernel U (S - n • T) = kernel U S - n • kernel U T := by
    exact (kernelLinear U).map_sub S (n • T) |>.trans
      (congrArg (fun z => kernel U S - z) (map_nsmul (kernelLinear U) n T))
  rw [hlin]
  change kernel U S y - n • kernel U T y = _
  rw [raw_kernel_at U hT]
  by_cases hy : y ∈ doubleCosetOrbit U g
  · rw [ite_eq_left hy, ite_eq_left hy, kernel_eq_of_same_orbit U S g hy hx, hn]
    simp
  · rw [ite_eq_right hy, ite_eq_right hy, smul_zero, sub_zero]

theorem kernel_sub_raw_support (S T : SphericalHecke U) {g : G}
    (hT : IsRawDoubleCoset U g T) {x : G ⧸ U} (hx : x ∈ doubleCosetOrbit U g)
    (n : ℕ) (hn : kernel U S x = (n : ℚ)) :
    (kernel U (S - n • T)).support ⊆ (kernel U S).support := by
  intro y hy
  rw [Finsupp.mem_support_iff, kernel_sub_raw_apply U S T hT hx n hn] at hy
  by_cases hmem : y ∈ doubleCosetOrbit U g
  · rw [ite_eq_left hmem] at hy
    exact False.elim (hy rfl)
  · rw [ite_eq_right hmem] at hy
    exact Finsupp.mem_support_iff.mpr hy

theorem natValued_sub_raw (S T : SphericalHecke U) {g : G}
    (hT : IsRawDoubleCoset U g T) {x : G ⧸ U} (hx : x ∈ doubleCosetOrbit U g)
    (n : ℕ) (hn : kernel U S x = (n : ℚ)) (hS : NatValuedKernel U (kernel U S)) :
    NatValuedKernel U (kernel U (S - n • T)) := by
  intro y
  rw [kernel_sub_raw_apply U S T hT hx n hn]
  split_ifs
  · exact ⟨0, rfl⟩
  · exact hS y

end

/-! Finite invariant natural kernels expand in raw orbit indicators.
The proof removes a complete orbit at each step. -/

open scoped Classical

variable {G I : Type*} [Group G] (U : Subgroup G)

theorem exists_raw_expansion (rep : I → G) (basis : I → SphericalHecke U)
    (hraw : ∀ i, IsRawDoubleCoset U (rep i) (basis i))
    (T : SphericalHecke U) (hT : NatValuedKernel U (kernel U T))
    (hcover : ∀ x ∈ (kernel U T).support, ∃ i, x ∈ doubleCosetOrbit U (rep i)) :
    ∃ c : I →₀ ℕ, T = c.sum (fun i n => n • basis i) := by
  suffices ∀ (s : Finset (G ⧸ U)) (S : SphericalHecke U),
      (kernel U S).support = s → NatValuedKernel U (kernel U S) →
      (∀ x ∈ s, ∃ i, x ∈ doubleCosetOrbit U (rep i)) →
      ∃ c : I →₀ ℕ, S = Finsupp.linearCombination ℕ basis c by
    exact this _ T rfl hT hcover
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro S hs hS hcov
    by_cases hempty : s = ∅
    · refine ⟨0, ?_⟩
      rw [map_zero]
      apply kernel_injective U
      exact Finsupp.support_eq_empty.mp (hs.trans hempty)
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨i, hi⟩ := hcov x hx
    obtain ⟨n, hn⟩ := hS x
    let R := S - n • basis i
    have hsub : (kernel U R).support ⊆ s := by
      rw [← hs]
      exact kernel_sub_raw_support U S (basis i) (hraw i) hi n hn
    have hnot : x ∉ (kernel U R).support := by
      rw [Finsupp.mem_support_iff, kernel_sub_raw_apply U S (basis i) (hraw i) hi n hn,
        ite_eq_left hi]
      exact not_not_intro rfl
    have hstrict : (kernel U R).support ⊂ s :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnot (heq.symm ▸ hx)⟩
    obtain ⟨c, hc⟩ := ih _ hstrict R rfl
      (natValued_sub_raw U S (basis i) (hraw i) hi n hn hS)
      (fun y hy => hcov y (hsub hy))
    refine ⟨c + Finsupp.single i n, ?_⟩
    rw [map_add, Finsupp.linearCombination_single]
    change S - n • basis i = _ at hc
    exact (sub_eq_iff_eq_add (a := S) (b := n • basis i)).mp hc

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel
