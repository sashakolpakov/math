import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActivePlace

/-! # Padic Embedding Place -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicEmbeddingPlace.Approximation

noncomputable section

/-! A Q_q-valued embedding of a number field is determined by its
finite place. The proof uses continuity on the actual completion. -/

open scoped Classical
open _root_.NumberField IsDedekindDomain

variable {q : ℕ} [Fact q.Prime]

theorem continuous_padic_ringHom_eq (f g : Padic q →+* Padic q)
    (hf : Continuous f) (hg : Continuous g) : f = g := by
  apply DFunLike.coe_injective
  apply (Padic.denseRange_ratCast q).equalizer hf hg
  funext r
  exact (map_ratCast f r).trans (map_ratCast g r).symm

theorem completion_ringHom_eq {V : Type*} [Field V] [TopologicalSpace V]
    (e : V ≃+* Padic q) (he : Continuous e.symm)
    (f g : V →+* Padic q) (hf : Continuous f) (hg : Continuous g) : f = g := by
  have h := continuous_padic_ringHom_eq
    (f.comp e.symm.toRingHom) (g.comp e.symm.toRingHom) (hf.comp he) (hg.comp he)
  ext x
  have hx := RingHom.congr_fun h (e x)
  change f (e.symm (e x)) = g (e.symm (e x)) at hx
  simpa only [RingEquiv.symm_apply_apply] using hx

variable (F : Type) [Field F] [NumberField F]

def finiteCompletionCongr {v w : HeightOneSpectrum (𝓞 F)} (h : v = w) :
    v.adicCompletion F ≃+* w.adicCompletion F := by
  subst w
  exact RingEquiv.refl _

theorem finiteCompletionCongr_continuous {v w : HeightOneSpectrum (𝓞 F)} (h : v = w) :
    Continuous (finiteCompletionCongr F h) := by
  subst w
  exact continuous_id

theorem finiteCompletionCongr_rational {v w : HeightOneSpectrum (𝓞 F)} (h : v = w) (x : F) :
    finiteCompletionCongr F h (FinitePlace.embedding v x) = FinitePlace.embedding w x := by
  subst w
  rfl

theorem padic_embeddingPlace_injective :
    Function.Injective (PELModuli.CMPoints.LocalPadic.embeddingPlace : (F →+* Padic q) → HeightOneSpectrum (𝓞 F)) := by
  intro f g h
  let e := PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv f
  let p := (PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv g).toRingHom.comp (finiteCompletionCongr F h).toRingHom
  have hp : Continuous p :=
    (PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_continuous g).comp (finiteCompletionCongr_continuous F h)
  have heq := completion_ringHom_eq e (PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_symm_continuous f)
    e.toRingHom p (PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_continuous f) hp
  ext x
  have hx := RingHom.congr_fun heq (FinitePlace.embedding (PELModuli.CMPoints.LocalPadic.embeddingPlace f) x)
  change PELModuli.CMPoints.LocalPadic.embeddingCompletionHom f (FinitePlace.embedding (PELModuli.CMPoints.LocalPadic.embeddingPlace f) x) =
    PELModuli.CMPoints.LocalPadic.embeddingCompletionHom g
      (finiteCompletionCongr F h (FinitePlace.embedding (PELModuli.CMPoints.LocalPadic.embeddingPlace f) x)) at hx
  rw [finiteCompletionCongr_rational, PELModuli.CMPoints.LocalPadic.embeddingCompletionHom_coe,
    PELModuli.CMPoints.LocalPadic.embeddingCompletionHom_coe] at hx
  exact hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicEmbeddingPlace.Approximation
