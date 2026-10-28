import OAI.AlgebraicGeometry.GroupSchemes.LocalObstruction

/-! # Kernel Ideal -/

namespace OAI.AlgebraicGeometry.GroupSchemes.KernelIdeal.FiniteEtale

noncomputable section

/-! Translate a kernel identity on every affine algebra into the defining coordinate ideal. -/

universe u

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

/-- The ideal pulled back from the augmentation by an algebra endomorphism. -/
def augmentationPullback (ε : A →ₐ[k] k) (m : A →ₐ[k] A) : Ideal A :=
  Ideal.span (m '' (RingHom.ker ε.toRingHom : Set A))

/-- Vanishing on the pulled-back augmentation ideal is exactly the constant-point equation. -/
theorem kills_augmentationPullback_iff (ε : A →ₐ[k] k) (m : A →ₐ[k] A)
    (f : A →ₐ[k] B) :
    augmentationPullback ε m ≤ RingHom.ker f.toRingHom ↔
      f.comp m = (Algebra.ofId k B).comp ε := by
  rw [augmentationPullback, Ideal.span_le]
  constructor
  · intro h
    ext x
    have hx : x - algebraMap k A (ε x) ∈ RingHom.ker ε.toRingHom := by
      change ε (x - algebraMap k A (ε x)) = 0
      simp
    have hz := h (Set.mem_image_of_mem m hx)
    change f (m (x - algebraMap k A (ε x))) = 0 at hz
    simpa only [map_sub, AlgHom.commutes, sub_eq_zero, AlgHom.comp_apply,
      Algebra.ofId_apply] using hz
  · intro h
    rintro _ ⟨x, hx, rfl⟩
    have he := AlgHom.congr_fun h x
    change ε x = 0 at hx
    change f (m x) = 0
    simpa only [AlgHom.comp_apply, Algebra.ofId_apply, hx, map_zero] using he

/-- The functor-of-points kernel property determines its ideal, even on nonreduced rings. -/
theorem kernel_eq_augmentationPullback (ε : A →ₐ[k] k) (m : A →ₐ[k] A)
    (q : A →ₐ[k] B)
    (hpoints : ∀ (T : CommAlgCat.{u} k) (f : A →ₐ[k] T),
      (∃ g : B →ₐ[k] T, g.comp q = f) ↔
        f.comp m = (Algebra.ofId k T).comp ε) :
    RingHom.ker q.toRingHom = augmentationPullback ε m := by
  apply le_antisymm
  · let I := augmentationPullback ε m
    let π := Ideal.Quotient.mkₐ k I
    have hπ : π.comp m = (Algebra.ofId k (A ⧸ I)).comp ε := by
      apply (kills_augmentationPullback_iff ε m π).mp
      change I ≤ RingHom.ker (Ideal.Quotient.mkₐ k I : A →+* A ⧸ I)
      rw [Ideal.Quotient.mkₐ_ker]
    obtain ⟨g, hg⟩ := (hpoints (CommAlgCat.of k (A ⧸ I)) π).mpr hπ
    intro x hx
    have he := AlgHom.congr_fun hg x
    change q x = 0 at hx
    have hz : π x = 0 := by simpa only [AlgHom.comp_apply, hx, map_zero] using he.symm
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · apply (kills_augmentationPullback_iff ε m q).mpr
    exact (hpoints (CommAlgCat.of k B) q).mp ⟨AlgHom.id k B, rfl⟩

end

end OAI.AlgebraicGeometry.GroupSchemes.KernelIdeal.FiniteEtale
