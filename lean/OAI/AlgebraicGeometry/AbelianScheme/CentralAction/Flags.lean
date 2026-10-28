import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

/-! # Flags -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Flags.Construction

noncomputable section

/-! A central relative position has exactly one possible superlattice.
The basis is constructed using the PID lattice theorem in Mathlib. -/

open scoped Pointwise

variable (q : ℕ) [Fact q.Prime]

theorem padic_lattice_basis (L : TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q]) :
    ∃ e : Module.Basis (Fin 3) ℚ_[q] (Fin 3 → ℚ_[q]),
      L.val = Submodule.span ℤ_[q] (Set.range e) := by
  have : Submodule.IsLattice ℚ_[q] L.val := L.property
  have hr : Module.finrank ℤ_[q] L.val = 3 := by
    simpa using Submodule.IsLattice.finrank_of_pi ℚ_[q] L.val
  let b := Module.finBasisOfFinrankEq ℤ_[q] L.val hr
  refine ⟨b.extendOfIsLattice ℚ_[q], ?_⟩
  have he : (b.extendOfIsLattice ℚ_[q] : Fin 3 → (Fin 3 → ℚ_[q])) = L.val.subtype ∘ b := by
    funext i
    exact b.extendOfIsLattice_apply ℚ_[q] i
  rw [he]
  change L.val = Submodule.span ℤ_[q] (Set.range (L.val.subtype ∘ b))
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

def centralScaledLattice (L : TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (a : ℤ) :
    TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q] :=
  ⟨(TateComparison.HeckeKernel.qUnit q ^ (-a)) • L.val, by
    have : Submodule.IsLattice ℚ_[q] L.val := L.property
    infer_instance⟩

theorem central_scaled_span (e : Module.Basis (Fin 3) ℚ_[q] (Fin 3 → ℚ_[q])) (a : ℤ) :
    (TateComparison.HeckeKernel.qUnit q ^ (-a)) • Submodule.span ℤ_[q] (Set.range e) =
      Submodule.span ℤ_[q] (Set.range fun i =>
        (algebraMap ℤ_[q] ℚ_[q] (q : ℤ_[q])) ^ (-a) • e i) := by
  simp only [Units.smul_def]
  rw [Submodule.smul_span, Set.smul_set_range]
  congr 1
  funext i
  simp [TateComparison.HeckeKernel.qUnit]

theorem relativePosition_constant_iff (L M : TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (a : ℤ) :
    TateComparison.Duality.RelativePosition (q : ℤ_[q]) (fun _ => a) L M ↔
      M = centralScaledLattice q L a := by
  constructor
  · rintro ⟨e, hL, hM⟩
    apply Subtype.ext
    change M.val = (TateComparison.HeckeKernel.qUnit q ^ (-a)) • L.val
    rw [hL, central_scaled_span, hM]
  · rintro rfl
    obtain ⟨e, he⟩ := padic_lattice_basis q L
    refine ⟨e, he, ?_⟩
    change (TateComparison.HeckeKernel.qUnit q ^ (-a)) • L.val = _
    rw [he, central_scaled_span]

variable {s : ℕ}

def centralSingletonFlag (L₀ : Fin s → TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q])
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v) :
    TateComparison.Duality.LinearBlockFlags (q : ℤ_[q]) L₀ [t] :=
  ⟨fun j v => if j = 0 then L₀ v else centralScaledLattice q (L₀ v) (a v), by
    refine ⟨by simp, ?_⟩
    intro j v
    fin_cases j
    have ht : t.val.exponent v = fun _ => a v := funext (ha v)
    simp only [List.length_cons, List.length_nil, List.get_eq_getElem,
      List.getElem_cons_zero, ht]
    exact (relativePosition_constant_iff q (L₀ v) _ (a v)).mpr rfl⟩

/-- There is a unique one-step linear flag for any integral central type. -/
theorem central_singleton_flag_unique
    (L₀ : Fin s → TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q])
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v)
    (F : TateComparison.Duality.LinearBlockFlags (q : ℤ_[q]) L₀ [t]) :
    F = centralSingletonFlag q L₀ t a ha := by
  apply Subtype.ext
  funext j v
  fin_cases j
  · exact congrFun F.property.1 v
  · have hp := F.property.2 (0 : Fin 1) v
    have ht : t.val.exponent v = fun _ => a v := funext (ha v)
    change TateComparison.Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent v) (F.val 0 v) (F.val 1 v) at hp
    rw [ht, relativePosition_constant_iff, F.property.1] at hp
    exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Flags.Construction
