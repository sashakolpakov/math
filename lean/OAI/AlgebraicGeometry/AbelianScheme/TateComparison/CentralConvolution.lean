import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # Central Convolution -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

noncomputable section

section

/-! The actual integral level is compact and open. Its finite orbits on
the discrete coset space give the raw spherical operators, without a
finiteness assumption or supplied double-coset basis. -/

open scoped Classical
open _root_.Topology

section Units

variable {R S : Type*} [Monoid R] [Monoid S]

theorem unitsMap_range (f : R →* S) (hf : Function.Injective f) :
    (Units.map f).range = (MonoidHom.mrange f).units := by
  ext u
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.val, rfl⟩, ⟨a.inv, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    let v : Rˣ := {
      val := a
      inv := b
      val_inv := by
        apply hf
        rw [map_mul, ha, hb, map_one]
        exact u.val_inv
      inv_val := by
        apply hf
        rw [map_mul, hb, ha, map_one]
        exact u.inv_val }
    exact ⟨v, Units.ext ha⟩

variable [TopologicalSpace R] [TopologicalSpace S]

theorem continuous_unitsMap (f : R →* S) (hf : Continuous f) :
    Continuous (Units.map f) :=
  Units.continuous_iff.mpr
    ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

omit [TopologicalSpace R] in
theorem isOpen_unitsMap_range (f : R →* S) (hf : Function.Injective f)
    (hopen : IsOpen (Set.range f)) : IsOpen ((Units.map f).range : Set Sˣ) := by
  rw [unitsMap_range f hf]
  exact Submonoid.isOpen_units (U := MonoidHom.mrange f) hopen

end Units

variable (s q : ℕ) [Fact q.Prime]

def padicMatrixInclusion : Matrix (Fin 3) (Fin 3) ℤ_[q] →+*
    Matrix (Fin 3) (Fin 3) ℚ_[q] :=
  RingHom.mapMatrix (PadicInt.Coe.ringHom (p := q))

theorem padicMatrixInclusion_isOpenEmbedding :
    IsOpenEmbedding (padicMatrixInclusion q) := by
  exact IsOpenEmbedding.piMap (fun _ : Fin 3 =>
    IsOpenEmbedding.piMap (fun _ : Fin 3 => PadicInt.isOpenEmbedding_coe))

theorem integralGL_range_open : IsOpen
    ((Matrix.GeneralLinearGroup.map (n := Fin 3) (PadicInt.Coe.ringHom (p := q))).range :
      Set (Matrix.GeneralLinearGroup (Fin 3) ℚ_[q])) :=
  isOpen_unitsMap_range (padicMatrixInclusion q).toMonoidHom
    (padicMatrixInclusion_isOpenEmbedding q).injective
    (padicMatrixInclusion_isOpenEmbedding q).isOpen_range

theorem integralUnits_range_open : IsOpen
    ((Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom).range : Set ℚ_[q]ˣ) :=
  isOpen_unitsMap_range (PadicInt.Coe.ringHom (p := q)).toMonoidHom
    PadicInt.isOpenEmbedding_coe.injective PadicInt.isOpenEmbedding_coe.isOpen_range

theorem integralLevel_mem_iff (g : HeckeKernel.SplitGroup s q) :
    g ∈ HeckeKernel.integralLevel s q ↔
      (∀ v, g.1 v ∈ (Matrix.GeneralLinearGroup.map
        (PadicInt.Coe.ringHom (p := q))).range) ∧
      g.2 ∈ (Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom).range := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun v => ⟨a.1 v, rfl⟩, ⟨a.2, rfl⟩⟩
  · rintro ⟨ha, ⟨b, hb⟩⟩
    choose a ha using ha
    exact ⟨(a, b), Prod.ext (funext ha) hb⟩

theorem integralLevel_open : IsOpen (HeckeKernel.integralLevel s q : Set (HeckeKernel.SplitGroup s q)) := by
  have h₁ : IsOpen {g : HeckeKernel.SplitGroup s q | ∀ v, g.1 v ∈
      (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q))).range} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun v =>
      (integralGL_range_open q).preimage ((continuous_apply v).comp continuous_fst))
  have h₂ := (integralUnits_range_open q).preimage
    (continuous_snd : Continuous (Prod.snd : HeckeKernel.SplitGroup s q → ℚ_[q]ˣ))
  have hset : (HeckeKernel.integralLevel s q : Set (HeckeKernel.SplitGroup s q)) =
      {g | (∀ v, g.1 v ∈ (Matrix.GeneralLinearGroup.map
        (PadicInt.Coe.ringHom (p := q))).range) ∧
        g.2 ∈ (Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom).range} :=
    Set.ext (integralLevel_mem_iff s q)
  rw [hset]
  exact h₁.inter h₂

theorem integralLevelMap_continuous : Continuous (HeckeKernel.integralLevelMap s q) := by
  have hGL : Continuous (Matrix.GeneralLinearGroup.map
      (PadicInt.Coe.ringHom (p := q)) :
        Matrix.GeneralLinearGroup (Fin 3) ℤ_[q] → Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :=
    continuous_unitsMap (padicMatrixInclusion q).toMonoidHom
      (padicMatrixInclusion_isOpenEmbedding q).continuous
  have hU : Continuous (Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom) :=
    continuous_unitsMap _ PadicInt.isOpenEmbedding_coe.continuous
  exact (continuous_pi fun v => hGL.comp ((continuous_apply v).comp continuous_fst)).prodMk
    (hU.comp continuous_snd)

theorem integralLevel_compact : IsCompact (HeckeKernel.integralLevel s q : Set (HeckeKernel.SplitGroup s q)) := by
  let : CompactSpace (Matrix (Fin 3) (Fin 3) ℤ_[q]) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → ℤ_[q]))
  exact isCompact_range (integralLevelMap_continuous s q)

section Orbits

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hcompact : IsCompact (U : Set G)) (hopen : IsOpen (U : Set G))

include hcompact hopen in
/-- A compact open subgroup has finite orbits on its discrete coset space. -/
theorem doubleCosetOrbit_finite (g : G) : (HeckeKernel.doubleCosetOrbit U g).Finite := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology_iff.mpr hopen
  have h : Continuous (fun u : U => (u : G) • (QuotientGroup.mk g⁻¹ : G ⧸ U)) :=
    by fun_prop
  exact (isCompact_range h).finite (IsDiscrete.univ.mono (Set.subset_univ _))

end Orbits

/-- The raw spherical basis is constructed from the actual integral level. -/
def sphericalBasis (t : Local.LocalType s) : HeckeKernel.Hecke s q :=
  HeckeKernel.rawHecke (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t)
    (doubleCosetOrbit_finite (HeckeKernel.integralLevel s q) (integralLevel_compact s q)
      (integralLevel_open s q) (HeckeKernel.representative s q t))

theorem sphericalBasis_isRaw (t : Local.LocalType s) :
    HeckeKernel.IsRawDoubleCoset (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t) (sphericalBasis s q t) :=
  HeckeKernel.rawHecke_isRaw _ _ _

end

/-! Central translations of raw kernels, the actual invertible central
operator, and clearing arbitrary cocharacters into the integral range. -/

open scoped Classical

section General

variable {G : Type*} [Group G] (U : Subgroup G)

theorem translate_apply (g : G) (k : HeckeKernel.CosetModule U) (x : G ⧸ U) :
    HeckeKernel.translate U g k x = k (g⁻¹ • x) := by
  have h := HeckeKernel.translate_apply_smul U g k (g⁻¹ • x)
  simpa only [smul_inv_smul] using h

theorem doubleCosetOrbit_central (z : G) (hz : ∀ g : G, Commute g z) :
    HeckeKernel.doubleCosetOrbit U z = {QuotientGroup.mk z⁻¹} := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    change (QuotientGroup.mk (u.val * z⁻¹) : G ⧸ U) = QuotientGroup.mk z⁻¹
    rw [(hz u.val).inv_right.eq]
    exact QuotientGroup.mk_mul_of_mem _ u.property
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨1, one_smul _ _⟩

theorem centralHeckeUnit_isRaw (z : G) (hz : ∀ g : G, Commute g z) :
    HeckeKernel.IsRawDoubleCoset U z (HeckeKernel.centralHeckeUnit U z hz).val := by
  intro x
  rw [HeckeKernel.centralHeckeUnit_kernel, ← HeckeKernel.mem_doubleCosetOrbit, doubleCosetOrbit_central U z hz]
  simp only [Finsupp.single_apply, Set.mem_singleton_iff, eq_comm]

theorem central_orbit_shift (z : G) (hz : ∀ g : G, Commute g z) (g : G) (x : G ⧸ U) :
    z • x ∈ HeckeKernel.doubleCosetOrbit U g ↔ x ∈ HeckeKernel.doubleCosetOrbit U (z * g) := by
  have hrep : (z * g)⁻¹ = z⁻¹ * g⁻¹ := by
    rw [mul_inv_rev, (hz g).inv_inv.eq]
  have htranslate (u : U) :
      u.val • (QuotientGroup.mk (z * g)⁻¹ : G ⧸ U) =
        z⁻¹ • (u.val • (QuotientGroup.mk g⁻¹ : G ⧸ U)) := by
    change QuotientGroup.mk (u.val * (z * g)⁻¹) =
      QuotientGroup.mk (z⁻¹ * (u.val * g⁻¹))
    rw [hrep, ← mul_assoc u.val, (hz u.val).inv_right.eq, mul_assoc]
  constructor
  · rintro ⟨u, hu⟩
    change (u : G) • (QuotientGroup.mk g⁻¹ : G ⧸ U) = z • x at hu
    exact ⟨u, (htranslate u).trans
      ((congrArg (fun y : G ⧸ U => z⁻¹ • y) hu).trans (inv_smul_smul z x))⟩
  · rintro ⟨u, hu⟩
    change (u : G) • (QuotientGroup.mk (z * g)⁻¹ : G ⧸ U) = x at hu
    have hu' := (htranslate u).symm.trans hu
    have h := congrArg (fun y : G ⧸ U => z • y) hu'
    refine ⟨u, ?_⟩
    simpa only [smul_inv_smul] using h

/-- Multiplication by the central raw operator translates the raw double coset. -/
theorem central_mul_isRaw (z : G) (hz : ∀ g : G, Commute g z)
    {g : G} {T : HeckeKernel.SphericalHecke U} (hT : HeckeKernel.IsRawDoubleCoset U g T) :
    HeckeKernel.IsRawDoubleCoset U (z * g) ((HeckeKernel.centralHeckeUnit U z hz).val * T) := by
  intro x
  change HeckeKernel.translate U z⁻¹ (HeckeKernel.kernel U T) (QuotientGroup.mk x) = _
  rw [translate_apply, inv_inv]
  change HeckeKernel.kernel U T (QuotientGroup.mk (z * x)) = _
  rw [hT, ← HeckeKernel.mem_doubleCosetOrbit, ← HeckeKernel.mem_doubleCosetOrbit]
  change (if z • (QuotientGroup.mk x : G ⧸ U) ∈ HeckeKernel.doubleCosetOrbit U g then 1 else 0) = _
  rw [central_orbit_shift U z hz]

theorem central_pow_mul_isRaw (z : G) (hz : ∀ g : G, Commute g z)
    {g : G} {T : HeckeKernel.SphericalHecke U} (hT : HeckeKernel.IsRawDoubleCoset U g T) (n : ℕ) :
    HeckeKernel.IsRawDoubleCoset U (z ^ n * g) ((HeckeKernel.centralHeckeUnit U z hz).val ^ n * T) := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using hT
  | succ n ih =>
    simpa only [pow_succ', mul_assoc] using central_mul_isRaw U z hz ih

end General

/-- Diagonal matrices assembled from units form a group homomorphism. -/
def diagonalHom {R : Type*} [CommRing R] :
    (Fin 3 → Rˣ) →* Matrix.GeneralLinearGroup (Fin 3) R where
  toFun := HeckeKernel.diagonalUnit
  map_one' := by
    apply Units.ext
    simp [HeckeKernel.diagonalUnit]
  map_mul' a b := by
    apply Units.ext
    simp [HeckeKernel.diagonalUnit, Matrix.diagonal_mul_diagonal]

variable (s q : ℕ) [Fact q.Prime]

theorem representative_shift (t : Local.LocalType s) (n : ℕ) :
    HeckeKernel.representative s q (t.shift n) = (HeckeKernel.centralElement s q) ^ n * HeckeKernel.representative s q t := by
  apply Prod.ext
  · funext v
    change diagonalHom (fun i => HeckeKernel.qUnit q ^ (t.exponent v i + (n : ℤ))) =
      (Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q)) ^ n *
        diagonalHom (fun i => HeckeKernel.qUnit q ^ t.exponent v i)
    have hscalar : Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q) =
        diagonalHom (fun _ => HeckeKernel.qUnit q) := by
      apply Units.ext
      rfl
    rw [hscalar, ← map_pow, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, Pi.pow_apply, zpow_add, zpow_natCast, mul_comm]
  · change HeckeKernel.qUnit q ^ (t.multiplier + 2 * (n : ℤ)) =
      (HeckeKernel.qUnit q ^ 2) ^ n * HeckeKernel.qUnit q ^ t.multiplier
    rw [zpow_add, zpow_mul, zpow_natCast, mul_comm]
    rfl

/-- The constructed central basis element is the explicit Hecke unit. -/
theorem sphericalBasis_central :
    sphericalBasis s q (Local.LocalType.central s) = (HeckeKernel.scalarHeckeUnit s q).val := by
  apply HeckeKernel.rawDoubleCoset_unique (HeckeKernel.integralLevel s q)
    (sphericalBasis_isRaw s q (Local.LocalType.central s))
  rw [HeckeKernel.representative_central]
  exact centralHeckeUnit_isRaw _ _ _

/-- Raw central translation has no additional degree factor. -/
theorem sphericalBasis_central_shift (t : Local.LocalType s) (n : ℕ) :
    sphericalBasis s q (Local.LocalType.central s) ^ n * sphericalBasis s q t =
      sphericalBasis s q (t.shift n) := by
  rw [sphericalBasis_central]
  apply HeckeKernel.rawDoubleCoset_unique (HeckeKernel.integralLevel s q) (g := HeckeKernel.representative s q (t.shift n))
  · rw [representative_shift]
    exact central_pow_mul_isRaw _ _ _ (sphericalBasis_isRaw s q t) n
  · exact sphericalBasis_isRaw s q (t.shift n)

/-- Every cocharacter is cleared by a power of the actual central raw operator. -/
theorem sphericalBasis_exists_integral_shift (t : Local.LocalType s) :
    ∃ (n : ℕ) (u : Local.IntegralType s),
      sphericalBasis s q (Local.LocalType.central s) ^ n * sphericalBasis s q t =
        sphericalBasis s q u.val := by
  obtain ⟨n, hn⟩ := Local.LocalType.exists_integral_shift t
  exact ⟨n, ⟨t.shift n, hn⟩, sphericalBasis_central_shift s q t n⟩

theorem sphericalBasis_central_isUnit : IsUnit (sphericalBasis s q (Local.LocalType.central s)) := by
  rw [sphericalBasis_central]
  exact (HeckeKernel.scalarHeckeUnit s q).isUnit

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution
