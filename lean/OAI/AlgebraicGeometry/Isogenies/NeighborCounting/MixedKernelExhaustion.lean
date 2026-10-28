import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups

/-! # Mixed Kernel Exhaustion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernelExhaustion

noncomputable section

/-! Exhaust the mixed kernel using the complementary Frobenius map.
The factorization [q] = F V and the transported etale q-torsion imply
that the active composite kernel lies in q-torsion. A restricted kernel
calculation then determines the whole kernel on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed.Construction OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction

variable {S : Scheme.{u}} {A B C E H : Over S} [GrpObj A] [GrpObj C]

omit [GrpObj C] in
theorem complement_kills_transported_torsion
    (f : A ⟶ B) (v : B ⟶ A) (q : ℕ) (hfv : f ≫ v = (𝟙 A) ^ q)
    (i : E ⟶ A) (j : H ⟶ B) (w : E ≅ H)
    (hsquare : w.hom ≫ j = i ≫ f) (hi : i ^ q = 1) : j ≫ v = 1 := by
  apply (cancel_epi w.hom).mp
  rw [← Category.assoc, hsquare, Category.assoc, hfv,
    MonObj.comp_pow, Category.comp_id, hi, MonObj.comp_one]

theorem supported_composite_kernel_killed
    (f : A ⟶ B) (v : B ⟶ A) (g : B ⟶ C) (q : ℕ) (hfv : f ≫ v = (𝟙 A) ^ q)
    (p : A ⟶ A) (r : B ⟶ B) (htransport : p ≫ f = f ≫ r)
    (j : H ⟶ B) (hjv : j ≫ v = 1)
    (hsecond : ∀ (T : Over S) (b : T ⟶ B), b ≫ r = b → b ≫ g = 1 →
      ∃ h : T ⟶ H, h ≫ j = b)
    (T : Over S) (a : T ⟶ A) (ha : a ≫ p = a) (hk : a ≫ f ≫ g = 1) : a ^ q = 1 := by
  have hs : (a ≫ f) ≫ r = a ≫ f := by
    rw [Category.assoc, ← htransport, ← Category.assoc, ha]
  obtain ⟨h, hh⟩ := hsecond T (a ≫ f) hs ((Category.assoc _ _ _).trans hk)
  have hkill : (a ≫ f) ≫ v = 1 := by
    rw [← hh, Category.assoc, hjv, MonObj.comp_one]
  rw [Category.assoc, hfv, MonObj.comp_pow, Category.comp_id] at hkill
  exact hkill

omit [GrpObj A] in
theorem prescribedKernel_of_kernel_factors {Q : Over S}
    (f : A ⟶ C) (c : Q ⟶ A) [Mono c] (j : H ⟶ Q)
    (hj : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (c ≫ f) j)
    (hfactor : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → ∃ z : T ⟶ Q, z ≫ c = a) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f (j ≫ c) := by
  intro T a
  constructor
  · intro ha
    obtain ⟨z, hz⟩ := hfactor T a ha
    have hz' : z ≫ (c ≫ f) = 1 := by rw [← Category.assoc, hz, ha]
    obtain ⟨h, hh, hu⟩ := (hj T z).mp hz'
    refine ⟨h, ?_, ?_⟩
    · change h ≫ (j ≫ c) = a
      rw [← Category.assoc, hh, hz]
    · intro h' hh'
      apply hu
      apply (cancel_mono c).mp
      exact (Category.assoc _ _ _).trans (hh'.trans hz.symm)
  · rintro ⟨h, hh, hu⟩
    have hz := (hj T (h ≫ j)).mpr ⟨h, rfl, fun h' he => by
      apply hu
      rw [← Category.assoc, he, Category.assoc]
      exact hh⟩
    have he : a ≫ f = (h ≫ j) ≫ (c ≫ f) := by
      rw [← hh]
      simp only [Category.assoc]
    exact he.trans hz

theorem prescribedKernel_from_qtorsion [IsCommMonObj A]
    (f : A ⟶ C) (q : ℕ) (j : H ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A q)
    (hj : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A q ≫ f) j)
    (hbound : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ^ q = 1) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f (j ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A q) :=
  prescribedKernel_of_kernel_factors f (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A q) j hj
    (fun T a ha => ⟨AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A q a (hbound T a ha),
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A q a (hbound T a ha)⟩)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernelExhaustion
