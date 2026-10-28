import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.Intrinsic
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleOpenCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenTopClass

/-! # Intrinsic Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicCoordinates.Intrinsic

noncomputable section

/-! The geometric selected-source comparison retains the original
single-sheaf coordinates and the actual appLE coefficient restriction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem paste {C : Type*} [Category C] {A B D P Q R : C}
    (a : A ⟶ B) (b : B ⟶ D) (p : A ⟶ P) (q : B ⟶ Q) (r : D ⟶ R)
    (x : P ⟶ Q) (y : Q ⟶ R) (ha : a ≫ q = p ≫ x) (hb : b ≫ r = q ≫ y) :
    (a ≫ b) ≫ r = p ≫ x ≫ y := by
  rw [Category.assoc, hb, ← Category.assoc a q, ha, Category.assoc]

private theorem inverse_coefficient {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B P Q : C} (e : A ≅ B) (a : B ⟶ P) (b : P ⟶ Q)
    (k : A ⟶ Q) (h : e.hom ≫ a ≫ b = k) :
    F.map e.inv ≫ F.map k = F.map a ≫ F.map b := by
  rw [← h, F.map_comp, F.map_comp, ← Category.assoc, ← F.map_comp,
    e.inv_hom_id, F.map_id, Category.id_comp]

variable {Y Z : Scheme.{0}} (π : Y ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U)
  (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
  (N : Y.Modules) {m : ℕ} (t : Fin m → Γ(Z,U)) (c : ℕ)

abbrev wide := OpenReindex.wideOpens π U hU
abbrev geometric := OpenReindex.geometricOpens π U hU V
abbrev native := Principal.AdditiveSections.opens V hV
abbrev reindex := OpenReindex.reindex π U V hVU
abbrev family := PrincipalPoint.Fraction.family U t
abbrev nativeFamily := (reindex π U V hVU).obj ∘ family U t
abbrev sections := Supported.SingleOpenCoordinates.sections N

def coefficientTransport : (geometric π U hU V).op ⋙ sections N ⟶
    (reindex π U V hVU ⋙ native V hV).op ⋙ sections N :=
  (Open.FunctorCoordinates.presheafIso (geometric π U hU V)
    (OpenReindex.opens_eq π U hU V hV hVU).symm (sections N)).hom

theorem coefficient :
    (OpenReindex.pushforwardIso π U hU N).hom ≫
      Functor.whiskerRight (NatTrans.op (OpenReindex.geometricInclusion π U hU V))
        (sections N) ≫ coefficientTransport π U hU V hV hVU N =
    OpenTopClass.coefficientMap π U hU V hV hVU N := by
  apply NatTrans.ext
  funext r
  dsimp only [coefficientTransport, NatTrans.comp_app]
  rw [Open.FunctorCoordinates.presheaf_component]
  change 𝟙 _ ≫ (sections N).map _ ≫ (sections N).map _ = 𝟙 _ ≫ (sections N).map _
  rw [Category.id_comp, Category.id_comp, ← (sections N).map_comp]
  congr 1

def wideCoordinates :=
  Supported.SingleOpenCoordinates.coordinates (family U t) (wide π U hU) N c m ≪≫
    homologyMapIso ((AugmentedOrdered.CechFunctor.functor (family U t)).mapIso
      (OpenReindex.pushforwardIso π U hU N).symm) m

abbrev nativeCoordinates := Supported.SingleOpenCoordinates.coordinates
  (nativeFamily π U V hVU t) (native V hV) N c m

def sourceMap :=
  AffinePrincipal.InjectiveRestriction.sourceMap (wide π U hU) (geometric π U hU V)
    (OpenReindex.geometricInclusion π U hU V) (family U t) N c ≫
  (Intrinsic.IntrinsicComparison.sourceIso π U hU V hV hVU t
    (Supported.SingleOpenCoordinates.originalSingle N c)).hom

theorem coefficient_comparison :
    (homologyMapIso ((AugmentedOrdered.CechFunctor.functor (family U t)).mapIso
      (OpenReindex.pushforwardIso π U hU N).symm) m).hom ≫
        homologyMap (OpenTopClass.complexMap π U hU V hV hVU N t) m =
    homologyMap (AugmentedOrdered.CechFunctor.complexMap (family U t)
      (Functor.whiskerRight (NatTrans.op (OpenReindex.geometricInclusion π U hU V))
        (sections N))) m ≫
      homologyMap (AugmentedOrdered.CechFunctor.complexMap (family U t)
        (coefficientTransport π U hU V hV hVU N)) m ≫
      homologyMap (AugmentedOrdered.CechReindex.iso (reindex π U V hVU)
        (family U t) (OpenTopClass.target V hV N)).hom m := by
  let H := AugmentedOrdered.CechFunctor.functor (family U t) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) m
  have h := inverse_coefficient H (OpenReindex.pushforwardIso π U hU N)
    (Functor.whiskerRight (NatTrans.op (OpenReindex.geometricInclusion π U hU V))
      (sections N)) (coefficientTransport π U hU V hV hVU N)
    (OpenTopClass.coefficientMap π U hU V hV hVU N)
    (coefficient π U hU V hV hVU N)
  have he := congrArg (fun a => a ≫
    homologyMap (AugmentedOrdered.CechReindex.iso (reindex π U V hVU)
      (family U t) (OpenTopClass.target V hV N)).hom m) h
  dsimp only [OpenTopClass.complexMap]
  rw [homologyMap_comp]
  simp only [Category.assoc] at he
  convert he using 1 <;> rfl

theorem comparison :
    homologyMap (sourceMap π U hU V hV hVU N t c) (m+c) ≫
      (nativeCoordinates π U V hV hVU N t c).hom =
    (wideCoordinates π U hU N t c).hom ≫
      homologyMap (OpenTopClass.complexMap π U hU V hV hVU N t) m := by
  have h₁ := Supported.SingleOpenCoordinates.restriction (family U t)
    (wide π U hU) N c m (geometric π U hU V)
    (OpenReindex.geometricInclusion π U hU V)
  have h₂ := Supported.SingleOpenCoordinates.congruence (family U t)
    (geometric π U hU V) N c m (OpenReindex.opens_eq π U hU V hV hVU).symm
  have h₃ := Supported.SingleOpenCoordinates.reindex (family U t) N c m
    (reindex π U V hVU) (native V hV)
  have h₁₂ := paste _ _ _ _ _ _ _ h₁ h₂
  have h₁₂₃ := paste _ _ _ _ _ _ _ h₁₂ h₃
  dsimp only [sourceMap, Intrinsic.IntrinsicComparison.sourceIso, Iso.trans_hom,
    Principal.PresheafReindex.sourceIso, wideCoordinates]
  simp only [homologyMap_comp, Category.assoc]
  rw [coefficient_comparison]
  simp only [Category.assoc] at h₁₂₃
  convert h₁₂₃ using 1 <;> rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicCoordinates.Intrinsic
