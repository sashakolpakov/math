import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFppfCovers
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Closed Sheafification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClosedSheafification

noncomputable section

/-! Fppf sheafification changes no sections at an algebraically closed
field point. Both directions follow from the actual local comparison
and the fact that every covering sieve there contains the identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem fppf_toSheafify_bijective_at_algClosed {S : Scheme} {K : Type} [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ S) (F : (Over S)ᵒᵖ ⥤ Type 1) :
    Function.Bijective ((toSheafify (Scheme.fppfTopology.over S) F).app (.op (Over.mk s))) := by
  let J := Scheme.fppfTopology.over S
  let φ := toSheafify J F
  constructor
  · intro a b h
    apply (Presheaf.equalizerSieve_eq_top_iff (F := F) (X := .op (Over.mk s)) a b).mp
    exact HilbertConstruction.ClosedFppfCovers.algClosed_over_fppf_cover_eq_top s _ (Presheaf.equalizerSieve_mem J φ a b h)
  · intro b
    have he := HilbertConstruction.ClosedFppfCovers.algClosed_over_fppf_cover_eq_top s _ (Presheaf.imageSieve_mem J φ b)
    have hi : Presheaf.imageSieve φ b (𝟙 (Over.mk s)) := by
      rw [he]
      trivial
    obtain ⟨a, ha⟩ := hi
    refine ⟨a, ?_⟩
    change φ.app (.op (Over.mk s)) a = (sheafify J F).map (𝟙 (.op (Over.mk s))) b at ha
    rw [Functor.map_id_apply] at ha
    exact ha

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClosedSheafification
