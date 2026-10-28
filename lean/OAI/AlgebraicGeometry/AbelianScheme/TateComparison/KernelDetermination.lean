import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeDetermination
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricQuotients

/-! # Kernel Determination -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Equality of actual Tate preimage lattices determines the complete
scheme kernels and the quotient group schemes, with their actions and
full markings. Geometric kernel bounds are extended to every test scheme
using the proved etaleness and represented-kernel descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricQuotients.Construction
variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k]
  {g N q m : ℕ} [Fact q.Prime]
  {P Q Q' : PEL.PELFamilyData R g N (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q (q ^ m)) (f : PELIsogenies.PELIsogeny P Q' (q ^ m))
  (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
  (hQ : Q.polarizationMap.HasPolarizationType δ)
  (hQ' : Q'.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

include δ hP hQ hq in
theorem PELIsogenies.PELIsogeny.kernel_killed_all_tests (T : Over (Spec (.of k)))
    (x : T ⟶ P.abelian.scheme) (hx : x ≫ e.isogeny.hom = 1) : x ^ (q ^ m) = 1 := by
  have : Etale e.isogeny.hom.left := CentralAction.PolarizationEtale.Construction.pelIsogeny_etale_of_polarization_type e δ hP
    (GeometricDivision.field_integer_unit_at_stalk (q ^ m))
  have : IsFinite (CentralAction.GroupKernel.Construction.groupKernelScheme e.isogeny.hom).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (CentralAction.GroupKernel.Construction.groupKernel_isPullback_left e.isogeny.hom) inferInstance
  have : Etale (CentralAction.GroupKernel.Construction.groupKernelScheme e.isogeny.hom).hom :=
    MorphismProperty.of_isPullback (P := @Etale)
      (CentralAction.GroupKernel.Construction.groupKernel_isPullback_left e.isogeny.hom) inferInstance
  have he := CentralAction.GeometricKernelDescent.Construction.kernel_inclusion_all_tests_of_geometric e.isogeny.hom
    ((𝟙 P.abelian.scheme) ^ (q ^ m)) (fun z hz => by
      rw [MonObj.comp_pow, Category.comp_id]
      exact e.geometricKernel_killed δ hP hQ hq z hz) T x hx
  simpa only [MonObj.comp_pow, Category.comp_id] using he

include δ hP hQ hQ' hq in
theorem PELIsogenies.PELIsogeny.geometric_kernel_eq_of_preimage_eq
    (h : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom)
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ P.abelian.scheme) :
    x ≫ e.isogeny.hom = 1 ↔ x ≫ f.isogeny.hom = 1 := by
  constructor
  · intro hx
    let z : Add.Tate.torsion q
        (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ P.abelian.scheme)) m :=
      ⟨Additive.ofMul x, congrArg Additive.ofMul (e.geometricKernel_killed δ hP hQ hq x hx)⟩
    exact (PELIsogenies.PELIsogeny.torsion_kernel_eq_of_preimage_eq q e f h z).mp hx
  · intro hx
    let z : Add.Tate.torsion q
        (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ P.abelian.scheme)) m :=
      ⟨Additive.ofMul x, congrArg Additive.ofMul (f.geometricKernel_killed δ hP hQ' hq x hx)⟩
    exact (PELIsogenies.PELIsogeny.torsion_kernel_eq_of_preimage_eq q e f h z).mpr hx

include δ hP hQ hQ' hq in
theorem PELIsogenies.PELIsogeny.kernel_eq_all_tests_of_preimage_eq
    (h : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom)
    (T : Over (Spec (.of k))) (x : T ⟶ P.abelian.scheme) :
    x ≫ e.isogeny.hom = 1 ↔ x ≫ f.isogeny.hom = 1 :=
  CentralAction.GeometricQuotients.Construction.pel_kernel_eq_all_tests_of_geometric e f δ hP (GeometricDivision.field_integer_unit_at_stalk (q ^ m))
    (GeometricDivision.field_integer_unit_at_stalk (q ^ m))
    (e.geometric_kernel_eq_of_preimage_eq f δ hP hQ hQ' hq h) T x

include δ hP hQ hQ' hq in
theorem PELIsogenies.PELIsogeny.exists_quotient_group_iso_of_preimage_eq
    (h : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom) :
    ∃ j : Q.abelian.scheme ≅ Q'.abelian.scheme,
      IsMonHom j.hom ∧ e.isogeny.hom ≫ j.hom = f.isogeny.hom ∧
      (∀ r : R, End.endSchemeMap Q.abelian.scheme (Q.action r) ≫ j.hom =
        j.hom ≫ End.endSchemeMap Q'.abelian.scheme (Q'.action r)) ∧
      ∀ (T : Over (Spec (.of k)))
        (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
        (Q.marking.hom.app (.op T) c).val ≫ j.hom = (Q'.marking.hom.app (.op T) c).val :=
  CentralAction.GeometricQuotients.Construction.exists_pel_quotient_group_iso_of_geometric_kernel e f δ hP
    (GeometricDivision.field_integer_unit_at_stalk (q ^ m)) (GeometricDivision.field_integer_unit_at_stalk (q ^ m))
    (e.geometric_kernel_eq_of_preimage_eq f δ hP hQ hQ' hq h)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
