import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRankAnnihilation
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionSheaves
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernels
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Coprime Torsion Is -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion

noncomputable section

/-!
# CartierDuality: coprime isogenies induce isomorphisms on actual torsion schemes

A faithfully flat cover supplies lifts. The coprime kernel calculation
corrects a lift into torsion, and effective descent constructs the inverse.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- A monomorphism through which an effective epimorphism factors is
an isomorphism when the factor map respects the covering relation. -/
theorem isIso_of_effectiveEpi_factor {C : Type*} [Category C]
    {P A B : C} (q : P ⟶ B) [EffectiveEpi q] (j : A ⟶ B) [Mono j]
    (a : P ⟶ A) (h : a ≫ j = q) : IsIso j := by
  have hrel : ∀ {T : C} (x y : T ⟶ P), x ≫ q = y ≫ q → x ≫ a = y ≫ a := by
    intro T x y hxy
    apply (cancel_mono j).mp
    simpa only [Category.assoc, h] using hxy
  let r := EffectiveEpi.desc q a hrel
  have hr : r ≫ j = 𝟙 B := by
    apply (cancel_epi q).mp
    rw [← Category.assoc, EffectiveEpi.fac, h, Category.comp_id]
  have hl : j ≫ r = 𝟙 A := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hr, Category.comp_id, Category.id_comp]
  exact ⟨⟨r, hl, hr⟩⟩

/-- Coprimality makes a homomorphism injective on n-torsion when its
kernel is killed by d. -/
theorem torsion_injective {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (n d : ℕ) (hnd : n.Coprime d)
    (hker : ∀ x : A, f x = 1 → x ^ d = 1)
    (a b : A) (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : f a = f b) : a = b := by
  apply div_eq_one.mp
  apply Picard.PoincareBundle.CoprimeKernels.eq_one_of_coprime_powers n d hnd (a / b)
  · rw [div_pow, ha, hb, div_self']
  · apply hker
    rw [map_div, hab, div_self']

/-- Any lift of a torsion point can be corrected to a torsion lift. -/
theorem exists_torsion_lift {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (n d : ℕ) (hnd : n.Coprime d)
    (hker : ∀ x : A, f x = 1 → x ^ d = 1) (x : A) (hx : (f x) ^ n = 1) :
    ∃ a : A, a ^ n = 1 ∧ f a = f x := by
  obtain ⟨⟨a, b⟩, hab⟩ := Picard.PoincareBundle.CoprimeKernels.kernelProductMap_surjective f n d hnd hker ⟨x, hx⟩
  have he : a.val * b.val = x := congrArg Subtype.val hab
  refine ⟨a.val, a.property, ?_⟩
  have hb : f b.val = 1 := b.property
  have h := congrArg f he
  simpa only [map_mul, hb, mul_one] using h

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B] (f : A ⟶ B) [IsMonHom f] (n : ℕ)

/-- The canonical morphism induced on the actual native torsion kernels. -/
def torsionMap : TorsionQuotient.SubgroupFunctor.torsionScheme A n ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme B n :=
  TorsionQuotient.SubgroupFunctor.torsionLift n (TorsionQuotient.SubgroupFunctor.torsionι A n ≫ f) (by
    rw [← MonObj.pow_comp]
    have h : (TorsionQuotient.SubgroupFunctor.torsionι A n) ^ n = 1 :=
      (TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (TorsionQuotient.SubgroupFunctor.torsionι A n)).mp ⟨𝟙 _, by simp⟩
    rw [h, MonObj.one_comp])

omit [IsCommMonObj B] in
theorem torsionMap_inclusion : torsionMap f n ≫ TorsionQuotient.SubgroupFunctor.torsionι B n = TorsionQuotient.SubgroupFunctor.torsionι A n ≫ f :=
  TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _

variable (d : ℕ) (hnd : n.Coprime d)
    (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ d = 1)

include hnd hker in
/-- The torsion map is a native monomorphism, tested on all S-schemes. -/
theorem torsionMap_mono : Mono (torsionMap f n) := by
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι A n) := inferInstanceAs (Mono (equalizer.ι ((𝟙 A) ^ n) (1 : A ⟶ A)))
  constructor
  intro T a b hab
  apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι A n)).mp
  apply torsion_injective (IsMonHom.monoidHom f T) n d hnd (hker T)
  · exact (TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (a ≫ TorsionQuotient.SubgroupFunctor.torsionι A n)).mp ⟨a, rfl⟩
  · exact (TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (b ≫ TorsionQuotient.SubgroupFunctor.torsionι A n)).mp ⟨b, rfl⟩
  · change (a ≫ TorsionQuotient.SubgroupFunctor.torsionι A n) ≫ f = (b ≫ TorsionQuotient.SubgroupFunctor.torsionι A n) ≫ f
    have h := congrArg (fun z => z ≫ TorsionQuotient.SubgroupFunctor.torsionι B n) hab
    simpa only [Category.assoc, torsionMap_inclusion] using h

include hnd hker in
/-- A faithfully flat quasi-compact group morphism induces an isomorphism
on n-torsion when its kernel is killed by an integer coprime to n. -/
theorem torsionMap_isIso [Flat f.left] [Surjective f.left] [QuasiCompact f.left] :
    IsIso (torsionMap f n) := by
  let P := pullback f (TorsionQuotient.SubgroupFunctor.torsionι B n)
  let a : P ⟶ A := pullback.fst f (TorsionQuotient.SubgroupFunctor.torsionι B n)
  let q : P ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme B n := pullback.snd f (TorsionQuotient.SubgroupFunctor.torsionι B n)
  have hs : IsPullback a.left q.left f.left (TorsionQuotient.SubgroupFunctor.torsionι B n).left :=
    (IsPullback.of_hasPullback f (TorsionQuotient.SubgroupFunctor.torsionι B n)).map (Over.forget S)
  have : Flat q.left := MorphismProperty.of_isPullback (P := @Flat) hs (inferInstanceAs (Flat f.left))
  have : Surjective q.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hs (inferInstanceAs (Surjective f.left))
  have : QuasiCompact q.left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hs (inferInstanceAs (QuasiCompact f.left))
  have : EffectiveEpi q := Picard.Homomorphisms.GroupDescent.Construction.effectiveEpi_over_of_fpqc q
  have ha : (a ≫ f) ^ n = 1 := by
    rw [show a ≫ f = q ≫ TorsionQuotient.SubgroupFunctor.torsionι B n from pullback.condition]
    exact (TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (q ≫ TorsionQuotient.SubgroupFunctor.torsionι B n)).mp ⟨q, rfl⟩
  obtain ⟨a', ha', hf⟩ := exists_torsion_lift (IsMonHom.monoidHom f P) n d hnd (hker P) a ha
  let j : P ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme A n := TorsionQuotient.SubgroupFunctor.torsionLift n a' ha'
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι B n) := inferInstanceAs (Mono (equalizer.ι ((𝟙 B) ^ n) (1 : B ⟶ B)))
  have hj : j ≫ torsionMap f n = q := by
    apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι B n)).mp
    rw [Category.assoc, torsionMap_inclusion, ← Category.assoc,
      show j ≫ TorsionQuotient.SubgroupFunctor.torsionι A n = a' from TorsionQuotient.SubgroupFunctor.torsionLift_ι n a' ha']
    change a' ≫ f = a ≫ f at hf
    exact hf.trans (show a ≫ f = q ≫ TorsionQuotient.SubgroupFunctor.torsionι B n from pullback.condition)
  have : Mono (torsionMap f n) := torsionMap_mono f n d hnd hker
  exact isIso_of_effectiveEpi_factor q (torsionMap f n) j hj

/-- Over a field, coprimality with the actual finite-flat degree makes
an isogeny's actual torsion map an isomorphism in every characteristic. -/
theorem torsionMap_isIso_of_coprime_degree
    {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (n : ℕ) (s : Spec (.of k)) (h : n.Coprime (f.left.finrank (η[B].left s))) :
    IsIso (torsionMap f n) :=
  torsionMap_isIso f n _ h (IntrinsicRankAnnihilation.Construction.NormCharacters.kernel_killed_by_degree k f s)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion
