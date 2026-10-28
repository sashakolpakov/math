import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilitySplit

/-! # Filtered Projection -/

namespace OAI.NumberTheory.PadicHodge.FilteredProjection.GeometricComparison

noncomputable section

/-! A filtration-preserving idempotent supplies the required filtered splitting. -/

namespace FiltrationTransport

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem projection_splits_step (F : GeometricComparison.Linear.FiniteFiltration K V) (P : Module.End K V)
    (hP : IsIdempotentElem P) (i : ℤ) (hi : F.step i ≤ (F.step i).comap P) :
    (P.range ⊓ F.step i) ⊔ (P.ker ⊓ F.step i) = F.step i := by
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  intro x hx
  apply Submodule.mem_sup.mpr
  refine ⟨P x, ⟨⟨x, rfl⟩, hi hx⟩, x - P x, ⟨?_, (F.step i).sub_mem hx (hi hx)⟩,
    add_sub_cancel _ _⟩
  change P (x - P x) = 0
  rw [P.map_sub, show P (P x) = P x from LinearMap.congr_fun hP.eq x, sub_self]

theorem commuting_range_stable (P φ : Module.End K V) (h : Commute P φ) :
    P.range ≤ P.range.comap φ := by
  rintro x ⟨y, rfl⟩
  exact ⟨φ y, LinearMap.congr_fun h.eq y⟩

theorem commuting_kernel_stable (P φ : Module.End K V) (h : Commute P φ) :
    P.ker ≤ P.ker.comap φ := by
  intro x hx
  change P (φ x) = 0
  have he := LinearMap.congr_fun h.eq x
  change P (φ x) = φ (P x) at he
  exact he.trans ((congrArg φ hx).trans φ.map_zero)

variable [FiniteDimensional K V]

def invariantRestriction (φ : V ≃ₗ[K] V) (S : Submodule K V)
    (hS : S ≤ S.comap φ.toLinearMap) : S ≃ₗ[K] S :=
  LinearEquiv.ofBijective (φ.toLinearMap.restrict hS) (by
    have hinj : Function.Injective (φ.toLinearMap.restrict hS) := by
      intro x y h
      apply Subtype.ext
      exact φ.injective (congrArg Subtype.val h)
    exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩)

theorem invariantRestriction_toLinearMap (φ : V ≃ₗ[K] V) (S : Submodule K V)
    (hS : S ≤ S.comap φ.toLinearMap) :
    (invariantRestriction φ S hS).toLinearMap = φ.toLinearMap.restrict hS := rfl

end FiltrationTransport

variable {q : ℕ} [Fact q.Prime]
  {V : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]

theorem weaklyAdmissible_projection (F : GeometricComparison.Linear.FiniteFiltration ℚ_[q] V)
    (φ : V ≃ₗ[ℚ_[q]] V) (h : GeometricComparison.Linear.WeaklyAdmissible q F φ)
    (P : Module.End ℚ_[q] V) (hP : IsIdempotentElem P)
    (hcomm : Commute P φ.toLinearMap)
    (hFil : ∀ i, F.step i ≤ (F.step i).comap P) :
    GeometricComparison.Linear.WeaklyAdmissible q (F.restrict P.range)
      (FiltrationTransport.invariantRestriction φ P.range
        (FiltrationTransport.commuting_range_stable P φ.toLinearMap hcomm)) :=
  GeometricComparison.WeakAdmissibilitySplit.weaklyAdmissible_split F φ h P.range P.ker (LinearMap.IsIdempotentElem.isCompl hP)
    (FiltrationTransport.commuting_range_stable P φ.toLinearMap hcomm)
    (FiltrationTransport.commuting_kernel_stable P φ.toLinearMap hcomm)
    (fun i => FiltrationTransport.projection_splits_step F P hP i (hFil i)) _ rfl

end

end OAI.NumberTheory.PadicHodge.FilteredProjection.GeometricComparison
