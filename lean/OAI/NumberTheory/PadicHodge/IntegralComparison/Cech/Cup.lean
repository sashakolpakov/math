import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Cup
import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.Cup

noncomputable section

/-! The Alexander–Whitney product on the native nonempty-product Čech
complex. The forgetful comparison is the canonical product comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w t

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type w} (U : ι → C) [UnivLE.{w, t}]

abbrev forgetRing : CommRingCat.{t} ⥤ AddCommGrpCat.{t} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

def cochainRing (P : Cᵒᵖ ⥤ CommRingCat.{t}) :
    CosimplicialObject CommRingCat.{t} :=
  (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve U)).obj P

def nativeComplex (P : Cᵒᵖ ⥤ CommRingCat.{t}) :
    CochainComplex AddCommGrpCat.{t} ℕ :=
  (NonemptyCechNerve.complexFunctor U).obj (P ⋙ forgetRing)

def comparison (P : Cᵒᵖ ⥤ CommRingCat.{t}) :
    Cosimplicial.Cup.complex (cochainRing U P) ≅ nativeComplex U P :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).mapIso
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.cosimplicialIso forgetRing
      (NonemptyCechNerve.nerve U) P)

def cup (P : Cᵒᵖ ⥤ CommRingCat.{t}) {p q : ℕ}
    (x : (nativeComplex U P).X p) (y : (nativeComplex U P).X q) :
    (nativeComplex U P).X (p + q) :=
  (comparison U P).hom.f (p + q)
    (Cosimplicial.Cup.cup (cochainRing U P)
      ((comparison U P).inv.f p x) ((comparison U P).inv.f q y))

def coefficientMap {P Q : Cᵒᵖ ⥤ CommRingCat.{t}} (f : P ⟶ Q) :
    nativeComplex U P ⟶ nativeComplex U Q :=
  (NonemptyCechNerve.complexFunctor U).map (Functor.whiskerRight f forgetRing)

def ringMap {P Q : Cᵒᵖ ⥤ CommRingCat.{t}} (f : P ⟶ Q) :
    cochainRing U P ⟶ cochainRing U Q :=
  (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve U)).map f

theorem comparison_natural {P Q : Cᵒᵖ ⥤ CommRingCat.{t}} (f : P ⟶ Q)
    (n : ℕ) :
    forgetRing.map ((ringMap U f).app ⦋n⦌) ≫ (comparison U Q).hom.f n =
      (comparison U P).hom.f n ≫ (coefficientMap U f).f n := by
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.piComparison_map forgetRing
    (fun i : ((NonemptyCechNerve.nerve U).obj (op ⦋n⦌)).I =>
      f.app (op (((NonemptyCechNerve.nerve U).obj (op ⦋n⦌)).obj i)))

theorem comparison_inverse_natural {P Q : Cᵒᵖ ⥤ CommRingCat.{t}} (f : P ⟶ Q)
    (n : ℕ) :
    (comparison U P).inv.f n ≫ forgetRing.map ((ringMap U f).app ⦋n⦌) =
      (coefficientMap U f).f n ≫ (comparison U Q).inv.f n := by
  let eP := (HomologicalComplex.eval _ _ n).mapIso (comparison U P)
  let eQ := (HomologicalComplex.eval _ _ n).mapIso (comparison U Q)
  symm
  apply (Iso.comp_inv_eq eQ).2
  change (coefficientMap U f).f n =
    ((comparison U P).inv.f n ≫ forgetRing.map ((ringMap U f).app ⦋n⦌)) ≫
      (comparison U Q).hom.f n
  exact (Iso.inv_hom_id_assoc eP _).symm.trans
    ((congrArg (fun g => (comparison U P).inv.f n ≫ g)
      (comparison_natural U f n).symm).trans (Category.assoc _ _ _).symm)

theorem cup_natural {P Q : Cᵒᵖ ⥤ CommRingCat.{t}} (f : P ⟶ Q)
    {p q : ℕ} (x : (nativeComplex U P).X p) (y : (nativeComplex U P).X q) :
    (coefficientMap U f).f (p + q) (cup U P x y) =
      cup U Q ((coefficientMap U f).f p x) ((coefficientMap U f).f q y) := by
  have hp := ConcreteCategory.congr_hom (comparison_inverse_natural U f p) x
  have hq := ConcreteCategory.congr_hom (comparison_inverse_natural U f q) y
  have h := ConcreteCategory.congr_hom (comparison_natural U f (p + q))
    (Cosimplicial.Cup.cup (cochainRing U P)
      ((comparison U P).inv.f p x) ((comparison U P).inv.f q y))
  change _ = (coefficientMap U f).f (p + q) (cup U P x y) at h
  change (ringMap U f).app ⦋p⦌ ((comparison U P).inv.f p x) = _ at hp
  change (ringMap U f).app ⦋q⦌ ((comparison U P).inv.f q y) = _ at hq
  exact h.symm.trans ((congrArg ((comparison U Q).hom.f (p + q))
    (Cosimplicial.Cup.cup_natural (cochainRing U P) (ringMap U f)
      ((comparison U P).inv.f p x) ((comparison U P).inv.f q y))).trans
    (congrArg ((comparison U Q).hom.f (p + q))
      (congrArg₂ (Cosimplicial.Cup.cup (cochainRing U Q)) hp hq)))

theorem cup_isCocycle (P : Cᵒᵖ ⥤ CommRingCat.{t}) {p q : ℕ}
    (x : (nativeComplex U P).X p) (y : (nativeComplex U P).X q)
    (hx : (nativeComplex U P).d p (p + 1) x = 0)
    (hy : (nativeComplex U P).d q (q + 1) y = 0) :
    (nativeComplex U P).d (p + q) (p + q + 1) (cup U P x y) = 0 := by
  have hxp : Cosimplicial.Cup.differential (cochainRing U P) p
      ((comparison U P).inv.f p x) = 0 := by
    have h := ConcreteCategory.congr_hom ((comparison U P).inv.comm p (p + 1)) x
    exact (Cosimplicial.Cup.complex_d_apply (cochainRing U P) p _).symm.trans
      (h.trans ((congrArg ((comparison U P).inv.f (p + 1)) hx).trans (map_zero _)))
  have hyp : Cosimplicial.Cup.differential (cochainRing U P) q
      ((comparison U P).inv.f q y) = 0 := by
    have h := ConcreteCategory.congr_hom ((comparison U P).inv.comm q (q + 1)) y
    exact (Cosimplicial.Cup.complex_d_apply (cochainRing U P) q _).symm.trans
      (h.trans ((congrArg ((comparison U P).inv.f (q + 1)) hy).trans (map_zero _)))
  have hz := Cosimplicial.Cup.cup_isCocycle (cochainRing U P) _ _ hxp hyp
  have hz' := (Cosimplicial.Cup.complex_d_apply (cochainRing U P) (p + q) _).trans hz
  have h := ConcreteCategory.congr_hom ((comparison U P).hom.comm (p + q) (p + q + 1))
    (Cosimplicial.Cup.cup (cochainRing U P)
      ((comparison U P).inv.f p x) ((comparison U P).inv.f q y))
  exact h.trans ((congrArg ((comparison U P).hom.f (p + q + 1)) hz').trans (map_zero _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.Cup
