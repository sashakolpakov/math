import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedRationalPoints
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-! # Closed Fppf Covers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFppfCovers

noncomputable section

/-! Every fppf covering sieve of an algebraically closed field point contains the identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

theorem algClosed_fppf_cover_id (R : Sieve (Spec (.of K)))
    (hR : R ∈ Scheme.fppfTopology (Spec (.of K))) : R (𝟙 _) := by
  have : Scheme.fppfPrecoverage.HasIsos := by
    constructor
    intro X Y f _
    exact (Scheme.singleton_mem_precoverage_iff _ f).mpr
      ⟨f.surjective, inferInstance, inferInstance⟩
  have : Scheme.fppfPrecoverage.HasPullbacks := by
    dsimp only [Scheme.fppfPrecoverage]
    infer_instance
  obtain ⟨P, hP, hPR⟩ :=
    Scheme.fppfPrecoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  have hcover := (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).mp hP.1
  obtain ⟨X, f, hf, x, _⟩ := hcover (IsLocalRing.closedPoint K)
  have : Nonempty X := ⟨x⟩
  have : LocallyOfFinitePresentation f := (hP.2 hf).2
  obtain ⟨s, hs⟩ := ClosedRationalPoints.nonempty_locallyFiniteType_exists_section f
  exact hs ▸ R.downward_closed (hPR X f hf) s

theorem algClosed_fppf_cover_eq_top (R : Sieve (Spec (.of K)))
    (hR : R ∈ Scheme.fppfTopology (Spec (.of K))) : R = ⊤ := by
  apply top_unique
  intro Y f _
  simpa using R.downward_closed (algClosed_fppf_cover_id R hR) f

theorem algClosed_over_fppf_cover_eq_top {S : Scheme.{u}} (s : Spec (.of K) ⟶ S)
    (R : Sieve (Over.mk s)) (hR : R ∈ (Scheme.fppfTopology.over S) (Over.mk s)) : R = ⊤ := by
  apply (Sieve.overEquiv (Over.mk s)).injective
  rw [OrderIso.map_top]
  exact algClosed_fppf_cover_eq_top _ ((Scheme.fppfTopology.mem_over_iff R).mp hR)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFppfCovers
