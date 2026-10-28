import OAI.RepresentationTheory.Theta.Geometric.Kernel
import OAI.RepresentationTheory.Theta.Geometric.DoubleCosets

/-! # Cosets -/

namespace OAI.RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical

noncomputable section

section

/-! The actual active-sector coset space in the full split similitude
group is the SL3 integral coset space. No active algebra equivalence is
assumed; this constructs its underlying coset identification. -/

variable (q : ℕ) [Fact q.Prime]

def integralUnits : Subgroup (ℚ_[q])ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom).range

def unitDetGL : Subgroup (SphericalGU.Spherical.GL3 q) :=
  (integralUnits q).comap Matrix.GeneralLinearGroup.det

theorem integralGL_unitDet {g : SphericalGU.Spherical.GL3 q} (hg : g ∈ SphericalGU.Spherical.integralGL3 q) :
    g ∈ unitDetGL q := by
  obtain ⟨U, rfl⟩ := hg
  refine ⟨U.det, ?_⟩
  exact (Matrix.GeneralLinearGroup.map_det (PadicInt.Coe.ringHom (p := q)) U).symm

theorem mem_integralSplitGU_iff {s : ℕ} (g : SphericalGU.Spherical.SplitGU q s) :
    g ∈ SphericalGU.Spherical.integralSplitGU q s ↔
      (∀ v, g.1 v ∈ SphericalGU.Spherical.integralGL3 q) ∧ g.2 ∈ integralUnits q := by
  constructor
  · rintro ⟨⟨U, m⟩, rfl⟩
    exact ⟨fun v => ⟨U v, rfl⟩, m, rfl⟩
  · rintro ⟨hU, m, hm⟩
    choose U hU using hU
    refine ⟨(U, m), ?_⟩
    apply Prod.ext
    · funext v
      exact hU v
    · exact hm

def activeAllowed {s : ℕ} (v : Fin s) : Subgroup (SphericalGU.Spherical.SplitGU q s) where
  carrier := {g | g.1 v ∈ unitDetGL q ∧
    (∀ w, w ≠ v → g.1 w ∈ SphericalGU.Spherical.integralGL3 q) ∧ g.2 ∈ integralUnits q}
  one_mem' := ⟨(unitDetGL q).one_mem, fun _ _ => (SphericalGU.Spherical.integralGL3 q).one_mem,
    (integralUnits q).one_mem⟩
  mul_mem' := by
    rintro g h ⟨hg, hg', hm⟩ ⟨hh, hh', hn⟩
    exact ⟨(unitDetGL q).mul_mem hg hh,
      fun w hw => (SphericalGU.Spherical.integralGL3 q).mul_mem (hg' w hw) (hh' w hw),
      (integralUnits q).mul_mem hm hn⟩
  inv_mem' := by
    rintro g ⟨hg, hg', hm⟩
    exact ⟨(unitDetGL q).inv_mem hg,
      fun w hw => (SphericalGU.Spherical.integralGL3 q).inv_mem (hg' w hw), (integralUnits q).inv_mem hm⟩

@[simp] theorem activeEmbedding_self {s : ℕ} (v : Fin s) (g : SphericalGU.Spherical.SL3 q) :
    (SphericalGU.Spherical.activeEmbedding q v g).1 v = Matrix.SpecialLinearGroup.toGL g := by
  simp [SphericalGU.Spherical.activeEmbedding]

theorem activeEmbedding_mem_allowed {s : ℕ} (v : Fin s) (g : SphericalGU.Spherical.SL3 q) :
    SphericalGU.Spherical.activeEmbedding q v g ∈ activeAllowed q v := by
  constructor
  · rw [activeEmbedding_self]
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) ∈ integralUnits q
    simpa only [Matrix.SpecialLinearGroup.coeToGL_det] using (integralUnits q).one_mem
  · constructor
    · intro w hw
      simpa only [SphericalGU.Spherical.activeEmbedding, MonoidHom.coe_mk, OneHom.coe_mk, ite_eq_right hw] using
        (SphericalGU.Spherical.integralGL3 q).one_mem
    · exact (integralUnits q).one_mem

theorem activeSector_le_allowed {s : ℕ} (v : Fin s) :
    SphericalGU.Spherical.activeSector q v ≤ activeAllowed q v := by
  apply sup_le
  · intro g hg
    obtain ⟨hb, hm⟩ := (mem_integralSplitGU_iff q g).mp hg
    exact ⟨integralGL_unitDet q (hb v), fun w _ => hb w, hm⟩
  · rintro _ ⟨g, rfl⟩
    exact activeEmbedding_mem_allowed q v g

theorem activeAllowed_factorization {s : ℕ} (v : Fin s)
    (g : SphericalGU.Spherical.SplitGU q s) (hg : g ∈ activeAllowed q v) :
    ∃ a : SphericalGU.Spherical.SL3 q, ∃ k : SphericalGU.Spherical.integralSplitGU q s, g = SphericalGU.Spherical.activeEmbedding q v a * k.val := by
  obtain ⟨hdet, hother, hmult⟩ := hg
  obtain ⟨u, hu⟩ := hdet
  have hd : ∃ u : ℤ_[q]ˣ,
      (g.1 v).val.det = PadicInt.Coe.ringHom (p := q) (u : ℤ_[q]) :=
    ⟨u, (congrArg Units.val hu).symm⟩
  obtain ⟨a, U, ha⟩ := Lattices.Spherical.determinant_one_representative q (DoubleCosets.Spherical.padic_determinant_adjustment q) (g.1 v) hd
  let k : SphericalGU.Spherical.SplitGU q s := (SphericalGU.Spherical.activeEmbedding q v a)⁻¹ * g
  have hk : k ∈ SphericalGU.Spherical.integralSplitGU q s := by
    apply (mem_integralSplitGU_iff q k).mpr
    constructor
    · intro w
      by_cases hw : w = v
      · subst w
        change (if v = v then Matrix.SpecialLinearGroup.toGL a else 1)⁻¹ * g.1 v ∈ SphericalGU.Spherical.integralGL3 q
        rw [ite_eq_left rfl, ha, inv_mul_cancel_left]
        exact ⟨U, rfl⟩
      · change (if w = v then Matrix.SpecialLinearGroup.toGL a else 1)⁻¹ * g.1 w ∈ SphericalGU.Spherical.integralGL3 q
        rw [ite_eq_right hw, inv_one, one_mul]
        exact hother w hw
    · change (1 : (ℚ_[q])ˣ)⁻¹ * g.2 ∈ integralUnits q
      simpa only [inv_one, one_mul] using hmult
  refine ⟨a, ⟨k, hk⟩, ?_⟩
  simp only [k, mul_inv_cancel_left]

/-- The generated active sector has exactly the determinant-unit active
condition, integral inactive blocks and an integral-unit multiplier. -/
theorem activeSector_eq_allowed {s : ℕ} (v : Fin s) :
    SphericalGU.Spherical.activeSector q v = activeAllowed q v := by
  apply le_antisymm (activeSector_le_allowed q v)
  intro g hg
  obtain ⟨a, k, rfl⟩ := activeAllowed_factorization q v g hg
  apply (SphericalGU.Spherical.activeSector q v).mul_mem
  · exact (show (SphericalGU.Spherical.activeEmbedding q v).range ≤ SphericalGU.Spherical.activeSector q v from le_sup_right) ⟨a, rfl⟩
  · exact (show SphericalGU.Spherical.integralSplitGU q s ≤ SphericalGU.Spherical.activeSector q v from le_sup_left) k.property

theorem activeEmbedding_integral_iff {s : ℕ} (v : Fin s) (g : SphericalGU.Spherical.SL3 q) :
    SphericalGU.Spherical.activeEmbedding q v g ∈ SphericalGU.Spherical.integralSplitGU q s ↔ g ∈ SphericalGU.Spherical.integralSL3 q := by
  constructor
  · intro hg
    have h := ((mem_integralSplitGU_iff q _).mp hg).1 v
    rw [activeEmbedding_self] at h
    exact (Lattices.Spherical.toGL_integral_iff q g).mp h
  · intro hg
    apply (mem_integralSplitGU_iff q _).mpr
    constructor
    · intro w
      change (if w = v then Matrix.SpecialLinearGroup.toGL g else 1) ∈ SphericalGU.Spherical.integralGL3 q
      split_ifs
      · exact (Lattices.Spherical.toGL_integral_iff q g).mpr hg
      · exact (SphericalGU.Spherical.integralGL3 q).one_mem
    · exact (integralUnits q).one_mem

def activeCosetMap {s : ℕ} (v : Fin s) :
    (SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) → (SphericalGU.Spherical.SplitGU q s ⧸ SphericalGU.Spherical.integralSplitGU q s) :=
  Quotient.map (SphericalGU.Spherical.activeEmbedding q v) (by
    intro g h hgh
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact (activeEmbedding_integral_iff q v (g⁻¹ * h)).mpr
      (QuotientGroup.leftRel_apply.mp hgh))

theorem activeCosetMap_injective {s : ℕ} (v : Fin s) :
    Function.Injective (activeCosetMap q v) := by
  intro c d
  induction c using Quotient.inductionOn with
  | h g =>
    induction d using Quotient.inductionOn with
    | h h =>
      intro heq
      apply QuotientGroup.eq.mpr
      apply (activeEmbedding_integral_iff q v (g⁻¹ * h)).mp
      rw [map_mul, map_inv]
      exact QuotientGroup.eq.mp heq

theorem activeCosetMap_mem {s : ℕ} (v : Fin s) (c : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) :
    activeCosetMap q v c ∈ SphericalGU.Spherical.activeOrbit q v := by
  induction c using Quotient.inductionOn with
  | h g =>
    refine ⟨SphericalGU.Spherical.activeEmbedding q v g, ?_, rfl⟩
    exact (show (SphericalGU.Spherical.activeEmbedding q v).range ≤ SphericalGU.Spherical.activeSector q v from le_sup_right) ⟨g, rfl⟩

def activeCosetToOrbit {s : ℕ} (v : Fin s) (c : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) :
    SphericalGU.Spherical.activeOrbit q v := ⟨activeCosetMap q v c, activeCosetMap_mem q v c⟩

/-- The complete active-sector lattice quotient is exactly the SL3 lattice
quotient, inside TateComparison's full split similitude group. -/
def activeCosetEquiv {s : ℕ} (v : Fin s) :
    (SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) ≃ SphericalGU.Spherical.activeOrbit q v :=
  Equiv.ofBijective (activeCosetToOrbit q v) ⟨by
    intro c d h
    exact activeCosetMap_injective q v (congrArg Subtype.val h), by
    rintro ⟨c, g, hg, hgc⟩
    obtain ⟨a, k, hak⟩ := activeAllowed_factorization q v g
      (activeSector_le_allowed q v hg)
    refine ⟨QuotientGroup.mk a, ?_⟩
    apply Subtype.ext
    change (QuotientGroup.mk (SphericalGU.Spherical.activeEmbedding q v a) :
      SphericalGU.Spherical.SplitGU q s ⧸ SphericalGU.Spherical.integralSplitGU q s) = c
    rw [← hgc]
    apply QuotientGroup.eq.mpr
    rw [hak, inv_mul_cancel_left]
    exact k.property⟩

theorem activeCosetMap_smul {s : ℕ} (v : Fin s) (g : SphericalGU.Spherical.SL3 q)
    (c : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) :
    activeCosetMap q v (g • c) = SphericalGU.Spherical.activeEmbedding q v g • activeCosetMap q v c := by
  induction c using Quotient.inductionOn with
  | h h =>
    change QuotientGroup.mk (SphericalGU.Spherical.activeEmbedding q v (g * h)) =
      QuotientGroup.mk (SphericalGU.Spherical.activeEmbedding q v g * SphericalGU.Spherical.activeEmbedding q v h)
    rw [map_mul]

end

section

/-! Linear transport of the actual active coset equivalence. The map into
the full coset module is extension by zero along the active coset embedding. -/

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

def activeModuleEquiv : SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q) ≃ₗ[ℚ] SphericalGU.Spherical.activeCosetModule q v :=
  (Finsupp.domLCongr (R := ℚ) (M := ℚ) (activeCosetEquiv q v)).trans
    (Finsupp.supportedEquivFinsupp (R := ℚ) (M := ℚ) (SphericalGU.Spherical.activeOrbit q v)).symm

def activeModuleMap : SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q) →ₗ[ℚ] SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSplitGU q s) :=
  Finsupp.lmapDomain ℚ ℚ (activeCosetMap q v)

@[simp] theorem activeModuleEquiv_single (c : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) (r : ℚ) :
    (activeModuleEquiv q v (Finsupp.single c r)).val =
      Finsupp.single (activeCosetMap q v c) r := by
  change ((Finsupp.supportedEquivFinsupp (R := ℚ) (M := ℚ) (SphericalGU.Spherical.activeOrbit q v)).symm
    (Finsupp.domLCongr (R := ℚ) (M := ℚ) (activeCosetEquiv q v) (Finsupp.single c r))).val = _
  rw [Finsupp.domLCongr_single, Finsupp.supportedEquivFinsupp_symm_single]
  rfl

theorem activeModuleEquiv_coe (w : SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q)) :
    (activeModuleEquiv q v w).val = activeModuleMap q v w := by
  have he : (SphericalGU.Spherical.activeCosetModule q v).subtype.comp (activeModuleEquiv q v).toLinearMap =
      activeModuleMap q v := by
    apply Finsupp.lhom_ext
    intro c r
    change (activeModuleEquiv q v (Finsupp.single c r)).val = _
    rw [activeModuleEquiv_single]
    simp [activeModuleMap]
  exact LinearMap.congr_fun he w

theorem activeModuleMap_injective : Function.Injective (activeModuleMap q v) :=
  Finsupp.mapDomain_injective (activeCosetMap_injective q v)

theorem activeModuleMap_translate (g : SphericalGU.Spherical.SL3 q) (w : SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q)) :
    activeModuleMap q v (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate (SphericalGU.Spherical.integralSL3 q) g w) =
      AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g) (activeModuleMap q v w) := by
  have he : (activeModuleMap q v).comp (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate (SphericalGU.Spherical.integralSL3 q) g) =
      (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g)).comp (activeModuleMap q v) := by
    apply Finsupp.lhom_ext
    intro c r
    simp [activeModuleMap, activeCosetMap_smul]
  exact LinearMap.congr_fun he w

@[simp] theorem activeModuleMap_identity :
    activeModuleMap q v (Finsupp.single (QuotientGroup.mk (1 : SphericalGU.Spherical.SL3 q)) 1) =
      Finsupp.single (QuotientGroup.mk (1 : SphericalGU.Spherical.SplitGU q s)) 1 := by
  change Finsupp.mapDomain (activeCosetMap q v) (Finsupp.single _ _) = _
  rw [Finsupp.mapDomain_single]
  change Finsupp.single (QuotientGroup.mk (SphericalGU.Spherical.activeEmbedding q v 1)) 1 = _
  rw [map_one]

end

/-! Restriction of actual full spherical operators to their preserved
active coset module. Multiplication is inherited from composition, and
the coset equivalence transports it to the SL3 convolution algebra. -/

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

def restrictActiveSpace (T : SphericalGU.Spherical.activeAlgebra q v) : Module.End ℚ (SphericalGU.Spherical.activeCosetModule q v) :=
  T.val.val.restrict (p := SphericalGU.Spherical.activeCosetModule q v) (q := SphericalGU.Spherical.activeCosetModule q v) T.property

def activeRestrictedOperator (T : SphericalGU.Spherical.activeAlgebra q v) : Module.End ℚ (SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q)) :=
  (activeModuleEquiv q v).symm.toLinearMap.comp
    ((restrictActiveSpace q v T).comp (activeModuleEquiv q v).toLinearMap)

theorem activeRestricted_transport (T : SphericalGU.Spherical.activeAlgebra q v) (w : SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q)) :
    activeModuleMap q v (activeRestrictedOperator q v T w) = T.val.val (activeModuleMap q v w) := by
  rw [← activeModuleEquiv_coe]
  change ((activeModuleEquiv q v)
    ((activeModuleEquiv q v).symm ((restrictActiveSpace q v T) ((activeModuleEquiv q v) w)))).val = _
  rw [LinearEquiv.apply_symm_apply]
  change T.val.val (activeModuleEquiv q v w).val = _
  rw [activeModuleEquiv_coe]

def activeRestriction (T : SphericalGU.Spherical.activeAlgebra q v) : SphericalGU.Spherical.SL3Hecke q :=
  ⟨activeRestrictedOperator q v T, by
    rintro _ ⟨g, rfl⟩
    apply LinearMap.ext
    intro w
    apply activeModuleMap_injective q v
    change activeModuleMap q v (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate (SphericalGU.Spherical.integralSL3 q) g (activeRestrictedOperator q v T w)) =
      activeModuleMap q v (activeRestrictedOperator q v T (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate (SphericalGU.Spherical.integralSL3 q) g w))
    simp only [activeModuleMap_translate, activeRestricted_transport]
    exact (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.hecke_translate (SphericalGU.Spherical.integralSplitGU q s) T.val (SphericalGU.Spherical.activeEmbedding q v g) _).symm⟩

def activeRestrictionHom : SphericalGU.Spherical.activeAlgebra q v →ₐ[ℚ] SphericalGU.Spherical.SL3Hecke q where
  toFun := activeRestriction q v
  map_zero' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    apply activeModuleMap_injective q v
    change activeModuleMap q v (activeRestrictedOperator q v _ w) = activeModuleMap q v 0
    rw [activeRestricted_transport, map_zero]
    rfl
  map_one' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    apply activeModuleMap_injective q v
    change activeModuleMap q v (activeRestrictedOperator q v _ w) = activeModuleMap q v w
    rw [activeRestricted_transport]
    rfl
  map_add' T U := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    apply activeModuleMap_injective q v
    change activeModuleMap q v (activeRestrictedOperator q v (T + U) w) =
      activeModuleMap q v (activeRestrictedOperator q v T w + activeRestrictedOperator q v U w)
    rw [map_add, activeRestricted_transport, activeRestricted_transport, activeRestricted_transport]
    rfl
  map_mul' T U := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    apply activeModuleMap_injective q v
    change activeModuleMap q v (activeRestrictedOperator q v (T * U) w) =
      activeModuleMap q v (activeRestrictedOperator q v T (activeRestrictedOperator q v U w))
    rw [activeRestricted_transport, activeRestricted_transport, activeRestricted_transport]
    rfl
  commutes' r := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    apply activeModuleMap_injective q v
    change activeModuleMap q v (activeRestrictedOperator q v (algebraMap ℚ (SphericalGU.Spherical.activeAlgebra q v) r) w) =
      activeModuleMap q v (r • w)
    rw [activeRestricted_transport, map_smul]
    rfl

theorem activeRestriction_kernel (T : SphericalGU.Spherical.activeAlgebra q v) :
    activeModuleMap q v (SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSL3 q) (activeRestrictionHom q v T)) =
      SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSplitGU q s) T.val := by
  have h := activeRestricted_transport q v T (Finsupp.single (QuotientGroup.mk (1 : SphericalGU.Spherical.SL3 q)) 1)
  rw [activeModuleMap_identity] at h
  exact h

theorem activeRestriction_injective : Function.Injective (activeRestrictionHom q v) := by
  intro T U h
  apply Subtype.ext
  apply AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel_injective (SphericalGU.Spherical.integralSplitGU q s)
  have hk := congrArg (fun S : SphericalGU.Spherical.SL3Hecke q => activeModuleMap q v (SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSL3 q) S)) h
  simpa only [activeRestriction_kernel] using hk

end

end OAI.RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical
