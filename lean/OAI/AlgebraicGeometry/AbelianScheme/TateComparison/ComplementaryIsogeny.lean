import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelDetermination

/-! # Complementary Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The proved full scheme-kernel bound constructs an actual complementary
group-scheme isogeny. Both compositions are the multiplier, and its effect
on the full marking is computed on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj BigOperators

namespace ComplementaryIsogeny.IsogenyComplement

variable {S : Scheme} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (f : A.Isogeny B) (n : ℕ)
  (hk : ∀ (T : Over S) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)

def hom : B.scheme ⟶ A.scheme := by
  have := CentralAction.Quotient.Construction.isogeny_effectiveEpi f
  exact EffectiveEpi.desc f.hom ((𝟙 A.scheme) ^ n)
    (CentralAction.Descent.Construction.kernel_inclusion_coequalizes f.hom ((𝟙 A.scheme) ^ n) (fun T x hx => by
      rw [MonObj.comp_pow, Category.comp_id]
      exact hk T x hx))

theorem comp_hom : f.hom ≫ IsogenyComplement.hom f n hk = (𝟙 A.scheme) ^ n := by
  have := CentralAction.Quotient.Construction.isogeny_effectiveEpi f
  exact EffectiveEpi.fac f.hom ((𝟙 A.scheme) ^ n)
    (CentralAction.Descent.Construction.kernel_inclusion_coequalizes f.hom ((𝟙 A.scheme) ^ n) (fun T x hx => by
      rw [MonObj.comp_pow, Category.comp_id]
      exact hk T x hx))

theorem hom_comp : IsogenyComplement.hom f n hk ≫ f.hom = (𝟙 B.scheme) ^ n := by
  have := CentralAction.Quotient.Construction.isogeny_effectiveEpi f
  apply (cancel_epi f.hom).mp
  rw [← Category.assoc, comp_hom, MonObj.pow_comp, Category.id_comp,
    MonObj.comp_pow, Category.comp_id]

instance hom_isMonHom : IsMonHom (IsogenyComplement.hom f n hk) := by
  have := CentralAction.Quotient.Construction.isogeny_tensor_epi f
  exact CentralAction.Quotient.Construction.isMonHom_of_factorization f.hom ((𝟙 A.scheme) ^ n) _ (comp_hom f n hk)

end ComplementaryIsogeny.IsogenyComplement

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k]
  {g N q m : ℕ} [Fact q.Prime]
  {P Q : PEL.PELFamilyData R g N (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q (q ^ m))
  (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
  (hQ : Q.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

def PELIsogenies.PELIsogeny.multiplierComplementHom : Q.abelian.scheme ⟶ P.abelian.scheme :=
  ComplementaryIsogeny.IsogenyComplement.hom e.isogeny (q ^ m) (e.kernel_killed_all_tests δ hP hQ hq)

instance PELIsogenies.PELIsogeny.multiplierComplementHom_isMonHom : IsMonHom (e.multiplierComplementHom δ hP hQ hq) :=
  ComplementaryIsogeny.IsogenyComplement.hom_isMonHom _ _ _

theorem PELIsogenies.PELIsogeny.comp_multiplierComplementHom :
    e.isogeny.hom ≫ e.multiplierComplementHom δ hP hQ hq = (𝟙 P.abelian.scheme) ^ (q ^ m) :=
  ComplementaryIsogeny.IsogenyComplement.comp_hom _ _ _

theorem PELIsogenies.PELIsogeny.multiplierComplementHom_comp :
    e.multiplierComplementHom δ hP hQ hq ≫ e.isogeny.hom = (𝟙 Q.abelian.scheme) ^ (q ^ m) :=
  ComplementaryIsogeny.IsogenyComplement.hom_comp _ _ _

theorem PELIsogenies.PELIsogeny.multiplierComplementHom_etale : Etale (e.multiplierComplementHom δ hP hQ hq).left := by
  let j := e.multiplierComplementHom δ hP hQ hq
  have : Etale e.isogeny.hom.left := CentralAction.PolarizationEtale.Construction.pelIsogeny_etale_of_polarization_type e δ hP
    (GeometricDivision.field_integer_unit_at_stalk (q ^ m))
  have : Etale (j.left ≫ e.isogeny.hom.left) := by
    rw [← Over.comp_left, PELIsogenies.PELIsogeny.multiplierComplementHom_comp]
    exact (GeometricDivision.multiplication_finite_etale Q.abelian (q ^ m)).2
  exact Etale.of_comp j.left e.isogeny.hom.left

def PELIsogenies.PELIsogeny.multiplierComplement : Q.abelian.Isogeny P.abelian := by
  let j := e.multiplierComplementHom δ hP hQ hq
  have : Etale j.left := e.multiplierComplementHom_etale δ hP hQ hq
  have : IsFinite (j.left ≫ e.isogeny.hom.left) := by
    rw [← Over.comp_left, PELIsogenies.PELIsogeny.multiplierComplementHom_comp]
    exact (GeometricDivision.multiplication_finite_etale Q.abelian (q ^ m)).1
  have : IsSeparated e.isogeny.hom.left := by
    have : IsSeparated (e.isogeny.hom.left ≫ Q.abelian.scheme.hom) := by
      rw [e.isogeny.hom.w]
      infer_instance
    exact IsSeparated.of_comp e.isogeny.hom.left Q.abelian.scheme.hom
  have : IsFinite j.left := IsFinite.of_comp j.left e.isogeny.hom.left
  have : Surjective (e.isogeny.hom.left ≫ j.left) := by
    rw [← Over.comp_left, PELIsogenies.PELIsogeny.comp_multiplierComplementHom]
    exact GeometricDivision.multiplication_surjective P.abelian (q ^ m)
  have : Surjective j.left := Surjective.of_comp e.isogeny.hom.left j.left
  exact ⟨j, inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem PELIsogenies.PELIsogeny.multiplierComplement_marking (T : Over (Spec (.of k)))
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (Q.marking.hom.app (.op T) c).val ≫ (e.multiplierComplement δ hP hQ hq).hom =
      (P.marking.hom.app (.op T) c).val ^ (q ^ m) := by
  change (Q.marking.hom.app (.op T) c).val ≫ e.multiplierComplementHom δ hP hQ hq = _
  rw [← e.marking T c, Category.assoc, PELIsogenies.PELIsogeny.comp_multiplierComplementHom,
    MonObj.comp_pow, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
