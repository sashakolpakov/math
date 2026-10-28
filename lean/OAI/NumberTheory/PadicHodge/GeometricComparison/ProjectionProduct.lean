import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Projection Product -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectionProduct.GeneralizedHecke

noncomputable section

/-! Products of commuting projections realize intersections of their actual ranges. -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem projection_mul_idempotent (P Q : Module.End K V)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (h : Commute P Q) :
    IsIdempotentElem (P * Q) := by
  change P * Q * (P * Q) = P * Q
  calc
    P * Q * (P * Q) = (P * P) * (Q * Q) := h.symm.mul_mul_mul_comm P Q
    _ = P * Q := congrArg₂ (· * ·) hP.eq hQ.eq

theorem projection_mul_range (P Q : Module.End K V)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (h : Commute P Q) :
    (P * Q).range = P.range ⊓ Q.range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨⟨Q y, rfl⟩, ⟨P y, ?_⟩⟩
    exact (LinearMap.congr_fun h.eq y).symm
  · rintro ⟨hx, hy⟩
    refine ⟨x, ?_⟩
    change P (Q x) = x
    rw [(LinearMap.IsIdempotentElem.mem_range_iff hQ).mp hy,
      (LinearMap.IsIdempotentElem.mem_range_iff hP).mp hx]

theorem product_preserves (P Q : Module.End K V) (U : Submodule K V)
    (hP : U ≤ U.comap P) (hQ : U ≤ U.comap Q) : U ≤ U.comap (P * Q) :=
  fun _ hx => hP (hQ hx)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectionProduct.GeneralizedHecke
