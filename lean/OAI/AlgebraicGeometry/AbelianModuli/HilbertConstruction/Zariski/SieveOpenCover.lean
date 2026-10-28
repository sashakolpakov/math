import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over

/-! # Sieve Open Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.SieveOpenCover

noncomputable section

/-! Every covering Zariski sieve contains an open-subset cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem zariskiSieve_exists_open {X : Scheme.{u}} (S : Sieve X)
    (hS : S ∈ Scheme.zariskiTopology X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ S U.ι := by
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  let i := 𝒰.idx x
  let U : X.Opens := (𝒰.f i).opensRange
  have hR : Set.range U.ι ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨y, rfl⟩
    exact y.property
  refine ⟨U, 𝒰.covers x, ?_⟩
  have h := S.downward_closed (h𝒰 _ _ (.mk i)) (IsOpenImmersion.lift (𝒰.f i) U.ι hR)
  simpa only [IsOpenImmersion.lift_fac] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.SieveOpenCover
