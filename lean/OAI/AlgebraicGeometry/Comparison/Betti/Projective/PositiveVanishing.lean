import OAI.AlgebraicGeometry.Comparison.Betti.ForgetModuleComplexHomology
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentComplex
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology

/-! # Positive Vanishing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveVanishing.Dolbeault

noncomputable section

section

/-! Original full-negative cycles give the same classes after forgetting algebraic scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Scheme.Modules

open OAI.AlgebraicGeometry.Comparison.Betti.ForgetModuleComplexHomology.Cech

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveLaurentNegativeCyclesLift (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    AddCommGrpCat.of (SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles (R := ℂ) (σ := Fin (n + 1)) d n) ⟶
      (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j d).cycles n :=
  (SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).map
    (SheafCohomology.Projective.TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToCycles (R := ℂ) j d n) ≫
      (ForgetModuleComplexHomology.Cech.moduleForgetComplexCyclesIso Γ(Spec (CommRingCat.of ℂ), ⊤)
        (SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := ℂ) j d) n).inv

theorem projectiveLaurentNegativeCyclesLift_i (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    projectiveLaurentNegativeCyclesLift n j d ≫ (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j d).iCycles n =
      AddCommGrpCat.ofHom (SheafCohomology.Projective.TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesAssembly
        (R := ℂ) (σ := Fin (n + 1)) d n).toAddMonoidHom := by
  rw [projectiveLaurentNegativeCyclesLift, Category.assoc, ForgetModuleComplexHomology.Cech.moduleForgetComplexCyclesIso_inv_i]
  have h := congrArg (SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).map
    (SheafCohomology.Projective.TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToCycles_i (R := ℂ) j d n)
  exact ((SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).map_comp _ _).symm.trans h

def projectiveLaurentNegativeCyclesHomologyIso (q : ℕ) (j : Fin (q + 2)) (d : ℤ) :
    AddCommGrpCat.of (SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles (R := ℂ) (σ := Fin (q + 2)) d (q + 1)) ≅
      (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex (q + 1) j d).homology (q + 1) :=
  (SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).mapIso
    (SheafCohomology.Projective.NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles (R := ℂ) j d q).symm.toModuleIso ≪≫
      (ForgetModuleComplexHomology.Cech.moduleForgetComplexHomologyIso Γ(Spec (CommRingCat.of ℂ), ⊤)
        (SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := ℂ) j d) (q + 1)).symm

theorem projectiveLaurentNegativeCyclesHomologyIso_hom (q : ℕ) (j : Fin (q + 2)) (d : ℤ) :
    (projectiveLaurentNegativeCyclesHomologyIso q j d).hom =
      projectiveLaurentNegativeCyclesLift (q + 1) j d ≫
        (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex (q + 1) j d).homologyπ (q + 1) := by
  change (SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).map
      (SheafCohomology.Projective.TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToHomology (R := ℂ) j d (q + 1)) ≫
        (ForgetModuleComplexHomology.Cech.moduleForgetComplexHomologyIso Γ(Spec (CommRingCat.of ℂ), ⊤)
          (SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := ℂ) j d) (q + 1)).inv = _
  rw [SheafCohomology.Projective.TwistCechHigher.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCyclesToHomology, Functor.map_comp,
    Category.assoc, ForgetModuleComplexHomology.Cech.moduleForgetComplexHomologyIso_inv_homologyπ]
  exact (Category.assoc _ _ _).symm

end

/-! Original algebraic Laurent cohomology vanishes off the positive top degree and for nonnegative twists. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.AlgebraicGeometry.Comparison.Betti.ForgetModuleComplexHomology.Cech

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveFullNegativeCochain_zero_of_ne_top (n : ℕ) (d : ℤ) (q : ℕ)
    (hq : q + 1 ≠ n)
    (s : SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{0, 0} (R := ℂ) (σ := Fin (n + 1)) d (q + 1)) : s = 0 := by
  funext e
  apply Subtype.ext
  funext a
  apply (s e).property
  intro hs
  have hsurj : Function.Surjective a.val := fun x => hs (by rw [e.property]; trivial)
  have hc := Fintype.card_congr (Equiv.ofBijective a.val ⟨a.property.injective, hsurj⟩)
  have hc' : q + 2 = n + 1 := by simpa using hc
  omega

theorem projectiveFullNegativeCochain_zero_nonneg (n : ℕ) (d : ℤ) (hd : 0 ≤ d) (q : ℕ)
    (s : SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{0, 0} (R := ℂ) (σ := Fin (n + 1)) d (q + 1)) : s = 0 := by
  funext e
  obtain ⟨i, hi⟩ := e.val.exists_not_mem_liftedNegativeSupport_of_nonneg (0 : Fin (n + 1)) hd
  exact (hi (by rw [e.property]; trivial)).elim

theorem projectiveAlgebraicLaurent_homology_subsingleton_of_fullNegative (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (q : ℕ)
    [Subsingleton (SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{0, 0} (R := ℂ) (σ := Fin (n + 1)) d (q + 1))] :
    Subsingleton ((LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j d).homology (q + 1)) := by
  let K := SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := ℂ) j d
  let E := SheafCohomology.Projective.NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles (R := ℂ) j d q
  let : Subsingleton ↥(SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles.{0, 0}
      (R := ℂ) (σ := Fin (n + 1)) d (q + 1)) :=
    ⟨fun s t => Subtype.ext (Subsingleton.elim s.val t.val)⟩
  let : Subsingleton (K.homology (q + 1)) := E.injective.subsingleton
  exact (ConcreteCategory.bijective_of_isIso
    (ForgetModuleComplexHomology.Cech.moduleForgetComplexHomologyIso Γ(Spec (CommRingCat.of ℂ), ⊤) K (q + 1)).hom).injective.subsingleton

theorem projectiveAlgebraicLaurent_homology_subsingleton_of_ne_top (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (q : ℕ) (hq : q + 1 ≠ n) :
    Subsingleton ((LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j d).homology (q + 1)) := by
  let : Subsingleton (SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{0, 0} (R := ℂ) (σ := Fin (n + 1)) d (q + 1)) :=
    ⟨fun s t => (projectiveFullNegativeCochain_zero_of_ne_top n d q hq s).trans
      (projectiveFullNegativeCochain_zero_of_ne_top n d q hq t).symm⟩
  exact projectiveAlgebraicLaurent_homology_subsingleton_of_fullNegative n j d q

theorem projectiveAlgebraicLaurent_homology_subsingleton_nonneg (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (hd : 0 ≤ d) (q : ℕ) :
    Subsingleton ((LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j d).homology (q + 1)) := by
  let : Subsingleton (SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{0, 0} (R := ℂ) (σ := Fin (n + 1)) d (q + 1)) :=
    ⟨fun s t => (projectiveFullNegativeCochain_zero_nonneg n d hd q s).trans
      (projectiveFullNegativeCochain_zero_nonneg n d hd q t).symm⟩
  exact projectiveAlgebraicLaurent_homology_subsingleton_of_fullNegative n j d q

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveVanishing.Dolbeault
