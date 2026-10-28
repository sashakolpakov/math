import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.SieveOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenModuleMaps

/-! # Zariski Open Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ZariskiOpenCover

noncomputable section

/-! Open-subset covers generate covering sieves on schemes over a base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} (T : Over X)

def relativeOpenCoverSieve {ι : Type v} (U : ι → T.left.Opens) : Sieve T :=
  Sieve.ofArrows (fun i => OpenModuleMaps.relativeOpen T (U i)) (fun i => OpenModuleMaps.relativeOpenInclusion T (U i))

theorem relativeOpenCoverSieve_mem {ι : Type v} (U : ι → T.left.Opens)
    (hU : ∀ x : T.left, ∃ i, x ∈ U i) :
    relativeOpenCoverSieve T U ∈ (Scheme.zariskiTopology.over X) T := by
  let 𝒰 : Scheme.OpenCover T.left := Scheme.Cover.mkOfCovers ι
    (fun i => (U i).toScheme) (fun i => (U i).ι) (by
      intro x
      obtain ⟨i, hi⟩ := hU x
      exact ⟨i, ⟨x, hi⟩, rfl⟩)
  rw [GrothendieckTopology.mem_over_iff, relativeOpenCoverSieve, Sieve.overEquiv_ofArrows]
  exact 𝒰.mem_grothendieckTopology

def relativeZariskiOpenIndex (S : Sieve T) :=
  {U : T.left.Opens // S (OpenModuleMaps.relativeOpenInclusion T U)}

theorem relativeZariskiOpenIndex_covers (S : Sieve T)
    (hS : S ∈ (Scheme.zariskiTopology.over X) T) (x : T.left) :
    ∃ i : relativeZariskiOpenIndex T S, x ∈ i.val := by
  obtain ⟨U, hx, hU⟩ := Zariski.SieveOpenCover.zariskiSieve_exists_open (Sieve.overEquiv T S) hS x
  exact ⟨⟨U, (Sieve.overEquiv_iff _ _).mp hU⟩, hx⟩

theorem relativeZariskiOpenCover_le (S : Sieve T) :
    relativeOpenCoverSieve T (fun i : relativeZariskiOpenIndex T S => i.val) ≤ S := by
  apply (Sieve.generate_le_iff _ _).mpr
  rintro Y f ⟨i⟩
  exact i.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ZariskiOpenCover
