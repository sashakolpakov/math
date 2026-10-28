import OAI.NumberTheory.PadicHodge.FilteredProjection

/-! # Fitting Generalized -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.FittingGeneralized.FittingFiltration
section

/-! The Fitting decomposition respects every invariant filtration subspace. -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def nilspace (T : Module.End K V) : Submodule K V := ⨆ n : ℕ, LinearMap.ker (T ^ n)

def invertibleSpace (T : Module.End K V) : Submodule K V := ⨅ n : ℕ, LinearMap.range (T ^ n)

theorem restricted_nilspace_le (T : Module.End K V) (U : Submodule K V)
    (hU : U ≤ U.comap T) :
    nilspace (T.restrict hU) ≤ (nilspace T).comap U.subtype := by
  apply iSup_le
  intro n x hx
  apply le_iSup (fun m : ℕ => LinearMap.ker (T ^ m)) n
  change (T ^ n) (x : V) = 0
  have h := congrArg Subtype.val hx
  change (((T.restrict hU) ^ n) x : V) = 0 at h
  erw [Module.End.pow_restrict n hU] at h
  exact h

theorem restricted_invertibleSpace_le (T : Module.End K V) (U : Submodule K V)
    (hU : U ≤ U.comap T) :
    invertibleSpace (T.restrict hU) ≤ (invertibleSpace T).comap U.subtype := by
  intro x hx
  change (x : V) ∈ invertibleSpace T
  simp only [invertibleSpace, Submodule.mem_iInf] at hx ⊢
  intro n
  obtain ⟨y, hy⟩ := hx n
  refine ⟨(y : V), ?_⟩
  have h := congrArg Subtype.val hy
  change (((T.restrict hU) ^ n) y : V) = (x : V) at h
  erw [Module.End.pow_restrict n hU] at h
  exact h

variable [FiniteDimensional K V]

theorem complement (T : Module.End K V) : IsCompl (nilspace T) (invertibleSpace T) :=
  LinearMap.isCompl_iSup_ker_pow_iInf_range_pow T

theorem splits_invariant (T : Module.End K V) (U : Submodule K V)
    (hU : U ≤ U.comap T) :
    (nilspace T ⊓ U) ⊔ (invertibleSpace T ⊓ U) = U := by
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  intro x hx
  have htop := (complement (T.restrict hU)).sup_eq_top
  have hmem : (⟨x, hx⟩ : U) ∈ nilspace (T.restrict hU) ⊔ invertibleSpace (T.restrict hU) := by
    rw [htop]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  exact Submodule.mem_sup.mpr ⟨(a : V), ⟨restricted_nilspace_le T U hU ha, a.property⟩,
    (b : V), ⟨restricted_invertibleSpace_le T U hU hb, b.property⟩, congrArg Subtype.val hab⟩

def projection (T : Module.End K V) : Module.End K V :=
  (nilspace T).projection (invertibleSpace T) (complement T)

theorem projection_idempotent (T : Module.End K V) : IsIdempotentElem (FittingFiltration.projection T) :=
  Submodule.isIdempotentElem_projection (complement T)

theorem projection_range (T : Module.End K V) : (FittingFiltration.projection T).range = nilspace T :=
  Submodule.range_projection (complement T)

theorem projection_preserves (T : Module.End K V) (U : Submodule K V)
    (hU : U ≤ U.comap T) : U ≤ U.comap (FittingFiltration.projection T) := by
  intro x hx
  rw [← splits_invariant T U hU] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  change FittingFiltration.projection T (a + b) ∈ U
  rw [map_add]
  have ha' : FittingFiltration.projection T a = a := Submodule.projection_apply_of_mem_left (complement T) ha.1
  have hb' : FittingFiltration.projection T b = 0 := Submodule.projection_apply_of_mem_right (complement T) hb.1
  rw [ha', hb', add_zero]
  exact ha.2

end

/-! The canonical Fitting projection commutes with every operator commuting with the original one. -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem nilspace_stable (T φ : Module.End K V) (h : Commute T φ) :
    nilspace T ≤ (nilspace T).comap φ := by
  apply Submodule.map_le_iff_le_comap.mp
  change (⨆ n : ℕ, LinearMap.ker (T ^ n)).map φ ≤ nilspace T
  rw [Submodule.map_iSup]
  apply iSup_le
  intro n
  exact (Submodule.map_le_iff_le_comap.mpr
    (FilteredProjection.GeometricComparison.FiltrationTransport.commuting_kernel_stable (T ^ n) φ (h.pow_left n))).trans
      (le_iSup (fun m : ℕ => LinearMap.ker (T ^ m)) n)

theorem invertibleSpace_stable (T φ : Module.End K V) (h : Commute T φ) :
    invertibleSpace T ≤ (invertibleSpace T).comap φ := by
  intro x hx
  change φ x ∈ invertibleSpace T
  simp only [invertibleSpace, Submodule.mem_iInf] at hx ⊢
  intro n
  exact FilteredProjection.GeometricComparison.FiltrationTransport.commuting_range_stable (T ^ n) φ (h.pow_left n) (hx n)

variable [FiniteDimensional K V]

theorem projection_kernel (T : Module.End K V) : (FittingFiltration.projection T).ker = invertibleSpace T :=
  Submodule.ker_projection (complement T)

theorem projection_commutes (T φ : Module.End K V) (h : Commute T φ) :
    Commute (FittingFiltration.projection T) φ := by
  apply (LinearMap.IsIdempotentElem.commute_iff (projection_idempotent T)).mpr
  rw [projection_range, projection_kernel]
  exact ⟨nilspace_stable T φ h, invertibleSpace_stable T φ h⟩

end NumberTheory.PadicHodge.GeometricComparison.FittingGeneralized.FittingFiltration

namespace NumberTheory.PadicHodge.GeometricComparison.FittingGeneralized.GeneralizedHecke

/-! Canonical projections onto generalized eigenspaces, with actual commutation and filtration preservation. -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def eigenProjection (T : Module.End K V) (μ : K) : Module.End K V :=
  FittingFiltration.projection (T - algebraMap K (Module.End K V) μ)

theorem eigenProjection_idempotent (T : Module.End K V) (μ : K) :
    IsIdempotentElem (eigenProjection T μ) := FittingFiltration.projection_idempotent _

theorem eigenProjection_range (T : Module.End K V) (μ : K) :
    (eigenProjection T μ).range = T.maxGenEigenspace μ := by
  rw [eigenProjection, FittingFiltration.projection_range, FittingFiltration.nilspace,
    ← Module.End.iSup_genEigenspace_eq]
  congr 1
  funext n
  rw [Module.End.genEigenspace_nat, Algebra.algebraMap_eq_smul_one]

theorem eigenProjection_commutes (T Z : Module.End K V) (μ : K) (h : Commute T Z) :
    Commute (eigenProjection T μ) Z :=
  FittingFiltration.projection_commutes _ Z
    (h.sub_left (Algebra.commute_algebraMap_left μ Z))

theorem eigenProjection_preserves (T : Module.End K V) (μ : K) (U : Submodule K V)
    (hU : U ≤ U.comap T) : U ≤ U.comap (eigenProjection T μ) := by
  apply FittingFiltration.projection_preserves
  intro x hx
  exact U.sub_mem (hU hx) (U.smul_mem μ hx)

end NumberTheory.PadicHodge.GeometricComparison.FittingGeneralized.GeneralizedHecke

end

end OAI
