import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ConcatenatedRegularity

/-! # Composite Section Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CompositeSectionKernel

noncomputable section

/-! Lifting generators of a section kernel through a closed-immersion
quotient gives the literal concatenated ambient ideal. -/

universe u v w
variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] {R : Type w} [CommRing R]

omit [CommRing A] in
theorem range_append {c m : ℕ} (s : Fin c → A) (t : Fin m → A) :
    Set.range (Fin.append s t) = Set.range s ∪ Set.range t := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Or.inl ⟨j, by simp⟩
    · exact Or.inr ⟨j, by simp⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd m i, by simp⟩
    · exact ⟨Fin.natAdd c j, by simp⟩

theorem kernel (f : A →+* B) (hf : Function.Surjective f) (ε : B →+* R)
    {c m : ℕ} (s : Fin c → A) (t : Fin m → A)
    (hs : Ideal.span (Set.range s) = RingHom.ker f)
    (ht : Ideal.span (Set.range (fun i => f (t i))) = RingHom.ker ε) :
    Ideal.span (Set.range (Fin.append s t)) = RingHom.ker (ε.comp f) := by
  have hm : (Ideal.span (Set.range t)).map f = RingHom.ker ε := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact ht
  rw [range_append, Ideal.span_union, ← RingHom.comap_ker, ← hm,
    Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot, hs]
  exact sup_comm _ _

def lift (f : A →+* B) (hf : Function.Surjective f) {m : ℕ} (t : Fin m → B) : Fin m → A :=
  fun i => Classical.choose (hf (t i))

theorem lift_eq (f : A →+* B) (hf : Function.Surjective f) {m : ℕ} (t : Fin m → B) (i : Fin m) :
    f (lift f hf t i) = t i := Classical.choose_spec (hf (t i))

theorem lifted_kernel (f : A →+* B) (hf : Function.Surjective f) (ε : B →+* R)
    {c m : ℕ} (s : Fin c → A) (t : Fin m → B)
    (hs : Ideal.span (Set.range s) = RingHom.ker f)
    (ht : Ideal.span (Set.range t) = RingHom.ker ε) :
    Ideal.span (Set.range (Fin.append s (lift f hf t))) = RingHom.ker (ε.comp f) := by
  apply kernel f hf ε s (lift f hf t) hs
  simpa only [lift_eq] using ht

theorem lifted_regular (f : A →+* B) (hf : Function.Surjective f)
    {c m : ℕ} (s : Fin c → A) (t : Fin m → B)
    (hs : Ideal.span (Set.range s) = RingHom.ker f)
    (hsreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn s))
    (htreg : RingTheory.Sequence.IsWeaklyRegular B (List.ofFn t)) :
    RingTheory.Sequence.IsWeaklyRegular A (List.ofFn (Fin.append s (lift f hf t))) := by
  apply Koszul.ConcatenatedRegularity.append_of_surjective f hf s (lift f hf t) hs hsreg
  simpa only [lift_eq] using htreg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CompositeSectionKernel
