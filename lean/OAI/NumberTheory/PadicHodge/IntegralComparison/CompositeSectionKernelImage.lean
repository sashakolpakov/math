import OAI.NumberTheory.PadicHodge.IntegralComparison.CompositeSectionKernel

/-! # Composite Section Kernel Image -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CompositeSectionKernelImage

noncomputable section

/-! The tail of a generating tuple for a composite section kernel
generates the section kernel after the surjective quotient. -/
universe u v w
variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] {R : Type w} [CommRing R]

theorem image_kernel (f : A →+* B) (hf : Function.Surjective f) (ε : B →+* R)
    {c m : ℕ} (s : Fin c → A) (t : Fin m → A)
    (hs : Ideal.span (Set.range s) = RingHom.ker f)
    (hst : Ideal.span (Set.range (Fin.append s t)) = RingHom.ker (ε.comp f)) :
    Ideal.span (Set.range (fun i => f (t i))) = RingHom.ker ε := by
  have hn : (Ideal.span (Set.range s)).map f = ⊥ := by
    rw [hs, RingHom.ker_eq_comap_bot, Ideal.map_comap_of_surjective f hf]
  have hp := congrArg (Ideal.map f) hst
  rw [CompositeSectionKernel.range_append, Ideal.span_union, Ideal.map_sup, hn, bot_sup_eq,
    ← RingHom.comap_ker, Ideal.map_comap_of_surjective f hf,
    Ideal.map_span, ← Set.range_comp] at hp
  exact hp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CompositeSectionKernelImage
