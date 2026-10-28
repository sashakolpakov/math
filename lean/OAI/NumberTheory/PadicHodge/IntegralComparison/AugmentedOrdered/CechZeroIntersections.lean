import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality

/-! # Cech Zero Intersections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZeroIntersections

noncomputable section

/-! If all positive intersections have zero coefficients, forgetting
support in the original augmented ordered Čech total is an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A]
  (L : CochainComplex (Cᵒᵖ ⥤ A) ℕ) [(CechFunctor.bicomplex U L).HasTotal (.up ℕ)]
  (hzero : ∀ p q, 0 < q → ∀ a : Cech.Index ι q,
    IsZero ((L.X p).obj (op ((Cech.formal U q).obj a))))

include hzero in
omit [(CechFunctor.bicomplex U L).HasTotal (ComplexShape.up ℕ)] in
theorem row_zero (p q : ℕ) (hq : q ≠ 0) : IsZero (((CechFunctor.bicomplex U L).X p).X q) := by
  change IsZero (∏ᶜ fun a : Cech.Index ι q => (L.X p).obj (op ((Cech.formal U q).obj a)))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Pi.hom_ext
  intro a
  exact (hzero p q (Nat.pos_of_ne_zero hq) a).eq_of_tgt _ _

def columnIso (n : ℕ) : ((CechFunctor.bicomplex U L).total (.up ℕ)).X n ≅ ((CechFunctor.bicomplex U L).X n).X 0 where
  hom := (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat
    (CechFunctor.bicomplex U L)) n 0 n
  inv := (CechFunctor.bicomplex U L).ιTotal (.up ℕ) n 0 n rfl
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    by_cases hq : q = 0
    · subst q
      have hp : p = n := by simpa using hpq
      subst p
      simp
    · exact (row_zero U L hzero p q hq).eq_of_src _ _
  inv_hom_id := by
    simpa only [Nat.add_zero] using
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_self
        (CechFunctor.bicomplex U L)) n 0

include hzero in
theorem forget_isIso : IsIso (CechForget.forgetSupport U L) := by
  let : ∀ n, IsIso ((CechForget.forgetSupport U L).f n) := fun n => by
    change IsIso ((columnIso U L hzero n).hom ≫ (CechZero.zeroIso U (L.X n)).hom)
    exact Iso.isIso_hom (columnIso U L hzero n ≪≫ CechZero.zeroIso U (L.X n))
  exact HomologicalComplex.Hom.isIso_of_components _

def iso := @asIso _ _ _ _ (CechForget.forgetSupport U L) (forget_isIso U L hzero)

include hzero in
theorem homology_isIso (n : ℕ) : IsIso (HomologicalComplex.homologyMap (CechForget.forgetSupport U L) n) := by
  exact Iso.isIso_hom (HomologicalComplex.homologyMapIso (iso U L hzero) n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZeroIntersections
