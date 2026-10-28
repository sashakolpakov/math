import OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothLocal

/-! # Smooth Kernel Quotient Local -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.SmoothKernelQuotientLocal.Constructions.LocalKernelNeighborhood

/-! # RiemannProjectivity: a finitely generated kernel vanishing in a stalk vanishes nearby -/

open scoped BigOperators

variable {A D : Type*} [CommRing A] [CommRing D]

theorem exists_annihilator (I : Ideal A) (hI : I.FG) (p : Ideal A) [p.IsPrime]
    (hzero : ∀ a ∈ I, algebraMap A (Localization.AtPrime p) a = 0) :
    ∃ s : A, s ∉ p ∧ ∀ a ∈ I, s * a = 0 := by
  classical
  obtain ⟨k, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hbI (i : Fin k) : b i ∈ I := by
    rw [← hb]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hd (i : Fin k) : ∃ s : p.primeCompl, s.val * b i = 0 :=
    (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) (b i)).mp
      (hzero (b i) (hbI i))
  choose t ht using hd
  let s : A := ∏ i, (t i).val
  have hs : s ∉ p := p.primeCompl.prod_mem (fun i _ => (t i).property)
  have hgen (i : Fin k) : s * b i = 0 := by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j : Fin k => (t j).val) (Finset.mem_univ i)
    change (∏ j, (t j).val) * b i = 0
    rw [hc, mul_right_comm, ht i, zero_mul]
  have hle : I ≤ (LinearMap.mul A A s).ker := by
    rw [← hb]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hgen i
  exact ⟨s, hs, fun a ha => hle ha⟩

theorem exists_localized_injective (f : A →+* D) (hfg : (RingHom.ker f).FG)
    (p : Ideal A) [p.IsPrime]
    (hzero : ∀ a, f a = 0 → algebraMap A (Localization.AtPrime p) a = 0) :
    ∃ s : A, s ∉ p ∧ Function.Injective (Localization.awayMap f s) := by
  obtain ⟨s, hs, hkill⟩ := exists_annihilator (RingHom.ker f) hfg p hzero
  refine ⟨s, hs, Localization.awayMap_injective_iff.mpr ?_⟩
  intro a ha
  exact ⟨1, by simpa using hkill a ha⟩

theorem exists_localized_bijective (f : A →+* D) (hf : Function.Surjective f)
    (hfg : (RingHom.ker f).FG) (p : Ideal A) [p.IsPrime]
    (hzero : ∀ a, f a = 0 → algebraMap A (Localization.AtPrime p) a = 0) :
    ∃ s : A, s ∉ p ∧ Function.Bijective (Localization.awayMap f s) := by
  obtain ⟨s, hs, hinj⟩ := exists_localized_injective f hfg p hzero
  refine ⟨s, hs, hinj, Localization.awayMap_surjective_iff.mpr ?_⟩
  intro a
  obtain ⟨b, hb⟩ := hf a
  exact ⟨b, 0, by simpa using hb⟩

end Geometry.ComplexTorus.RiemannProjectivity.SmoothKernelQuotientLocal.Constructions.LocalKernelNeighborhood

namespace Geometry.ComplexTorus.RiemannProjectivity.SmoothKernelQuotientLocal.Constructions.SmoothDominantQuotient

/-! # RiemannProjectivity: smooth neighborhoods in dominant algebraic quotients -/

variable {R A D : Type*} [CommRing R] [IsDomain R] [CommRing A] [CommRing D] [IsDomain D]
  [Algebra ℂ R] [Algebra ℂ A] [Algebra ℂ D] [Algebra R A] [Algebra R D]
  [IsScalarTower ℂ R A] [IsScalarTower ℂ R D]
  [Algebra.IsAlgebraic R A] [Algebra.Smooth ℂ A]

theorem exists_smooth_neighborhood (f : A →ₐ[R] D) (hf : Function.Surjective f)
    (hinj : Function.Injective (algebraMap R D)) (hfg : (RingHom.ker f.toRingHom).FG)
    (p : Ideal A) [p.IsPrime] (hp : RingHom.ker f.toRingHom ≤ p) :
    ∃ s : A, s ∉ p ∧ Algebra.Smooth ℂ (Localization.Away (f s)) := by
  obtain ⟨s, hs, hbij⟩ := LocalKernelNeighborhood.exists_localized_bijective
    f.toRingHom hf hfg p (SmoothLocal.Constructions.SmoothLocalKernel.kernel_vanishes_of_smooth f hinj p hp)
  let : Algebra.Smooth A (Localization.Away s) := Algebra.Smooth.of_isLocalization_Away s
  let : Algebra.Smooth ℂ (Localization.Away s) := Algebra.Smooth.comp ℂ A _
  let g : Localization.Away s →ₐ[ℂ] Localization.Away (f s) :=
    Localization.awayMapₐ (f.restrictScalars ℂ) s
  have hg : Function.Bijective g := hbij
  exact ⟨s, hs, Algebra.Smooth.of_equiv (AlgEquiv.ofBijective g hg)⟩

end Geometry.ComplexTorus.RiemannProjectivity.SmoothKernelQuotientLocal.Constructions.SmoothDominantQuotient

namespace Geometry.ComplexTorus.RiemannProjectivity.SmoothKernelQuotientLocal.Constructions.SmoothKernelQuotient

/-! # RiemannProjectivity: equations vanishing in a faithful analytic branch give smooth quotients locally -/

variable {R A D : Type*} [CommRing R] [IsDomain R] [CommRing A] [CommRing D] [IsDomain D]
  [Algebra R A] [Algebra R D] [Algebra.IsAlgebraic R A]
  [Algebra ℂ A] [Algebra.Smooth ℂ A]

theorem exists_smooth_neighborhood (f : A →ₐ[R] D)
    (hinj : Function.Injective (algebraMap R D)) (I : Ideal A) (hI : I.FG)
    (hIf : I ≤ RingHom.ker f.toRingHom) (p : Ideal A) [p.IsPrime]
    (hp : RingHom.ker f.toRingHom ≤ p) :
    ∃ s : A, s ∉ p ∧ Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk I s)) := by
  have hzero (a : A) (ha : Ideal.Quotient.mk I a = 0) :
      algebraMap A (Localization.AtPrime p) a = 0 :=
    SmoothLocal.Constructions.SmoothLocalKernel.kernel_vanishes_of_smooth f hinj p hp a
      (hIf (Ideal.Quotient.eq_zero_iff_mem.mp ha))
  have hfg : (RingHom.ker (Ideal.Quotient.mk I)).FG := by simpa using hI
  obtain ⟨s, hs, hbij⟩ := LocalKernelNeighborhood.exists_localized_bijective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hfg p hzero
  let : Algebra.Smooth A (Localization.Away s) := Algebra.Smooth.of_isLocalization_Away s
  let : Algebra.Smooth ℂ (Localization.Away s) := Algebra.Smooth.comp ℂ A _
  let g := Localization.awayMapₐ (Ideal.Quotient.mkₐ ℂ I) s
  have hg : Function.Bijective g := hbij
  exact ⟨s, hs, Algebra.Smooth.of_equiv (AlgEquiv.ofBijective g hg)⟩

end Geometry.ComplexTorus.RiemannProjectivity.SmoothKernelQuotientLocal.Constructions.SmoothKernelQuotient

end

end OAI
