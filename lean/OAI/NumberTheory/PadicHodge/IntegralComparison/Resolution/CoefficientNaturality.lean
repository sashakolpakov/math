import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CoefficientShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomologyTripleNaturality

/-! # Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CoefficientNaturality

noncomputable section

/-! The actual augmented source-resolution comparison with Ext commutes
with coefficient morphisms in every degree. -/

open _root_.CategoryTheory

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.CoefficientNaturality

universe u v z t

private theorem comparison_square {D : Type*} [Category D]
    {A B A' B' M M' : D} (e : A ≅ B) (e' : A' ≅ B') (s : A ≅ M) (s' : A' ≅ M')
    (f : B ⟶ B') (a : A ⟶ A') (b : M ⟶ M')
    (h : e.hom ≫ f = a ≫ e'.hom) (hs : a ≫ s'.hom = s.hom ≫ b) :
    f ≫ (e'.inv ≫ s'.hom) = (e.inv ≫ s.hom) ≫ b := by
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (f ≫ (e'.inv ≫ s'.hom)) = (e.hom ≫ f) ≫ (e'.inv ≫ s'.hom) :=
      (Category.assoc _ _ _).symm
    _ = (a ≫ e'.hom) ≫ (e'.inv ≫ s'.hom) := congrArg (fun x => x ≫ (e'.inv ≫ s'.hom)) h
    _ = a ≫ s'.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = s.hom ≫ b := hs
    _ = e.hom ≫ ((e.inv ≫ s.hom) ≫ b) := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {Y Y' : C} (g : Y ⟶ Y')

private theorem transport_map {Z : C} {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} Z Y d) (e' : V ≃ₗ[R] Ext.{z} Z Y' d)
    (a : ModuleCat.of R U ⟶ ModuleCat.of R V)
    (h : a ≫ e'.toModuleIso.hom = e.toModuleIso.hom ≫ IntegralComparison.Ext.CoefficientNaturality.component R g d Z) :
    a ≫ (hd ▸ e').toModuleIso.hom = (hd ▸ e).toModuleIso.hom ≫ IntegralComparison.Ext.CoefficientNaturality.component R g d' Z := by
  subst d'
  exact h

variable (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ}
  (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hK' : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y' (q + 1)))

theorem short_zero : ShortComplex.homologyMap (IntegralComparison.Ext.CoefficientNaturality.shortMap R g 0 (Augmented.ResolutionCycles.differentialSequence K 0)) ≫
    (Contravariant.Resolution.Comparison.shortHomologyIso R Y' K ι hK' 0).hom =
      (Contravariant.Resolution.Comparison.shortHomologyIso R Y K ι hK 0).hom ≫
        IntegralComparison.Ext.CoefficientNaturality.component R g 1 Z.unop := by
  let : Subsingleton (Ext.{z} (K.X 0).unop Y 1) := hK 0 0
  let : Subsingleton (Ext.{z} (K.X 0).unop Y' 1) := hK' 0 0
  exact IntegralComparison.Ext.CoefficientNaturality.short_homology R g (Augmented.ResolutionCycles.differentialSequence K 0)
    (Augmented.ResolutionCycles.augmentation K ι) (Augmented.ResolutionCycles.initialSequence K ι).zero
    (Augmented.ResolutionCycles.initialSequence_shortExact K ι)

theorem short_succ (n : ℕ) :
    ShortComplex.homologyMap (IntegralComparison.Ext.CoefficientNaturality.shortMap R g 0 (Augmented.ResolutionCycles.differentialSequence K (n + 1))) ≫
      (Contravariant.Resolution.Comparison.shortHomologyIso R Y' K ι hK' (n + 1)).hom =
        (Contravariant.Resolution.Comparison.shortHomologyIso R Y K ι hK (n + 1)).hom ≫
          IntegralComparison.Ext.CoefficientNaturality.component R g (n + 1 + 1) Z.unop := by
  let : Subsingleton (Ext.{z} (K.X (n + 1)).unop Y 1) := hK (n + 1) 0
  let : Subsingleton (Ext.{z} (K.X (n + 1)).unop Y' 1) := hK' (n + 1) 0
  let eY := Contravariant.ResolutionShift.cycleExtEquiv R Y K ι hK n 0
  let eY' := Contravariant.ResolutionShift.cycleExtEquiv R Y' K ι hK' n 0
  let hc : n + 0 + 2 = n + 1 + 1 := by omega
  have hs : IntegralComparison.Ext.CoefficientNaturality.component R g 1 (Augmented.ResolutionCycles.differentialSequence K n).cycles.unop ≫
      (hc ▸ eY').toModuleIso.hom = (hc ▸ eY).toModuleIso.hom ≫
        IntegralComparison.Ext.CoefficientNaturality.component R g (n + 1 + 1) Z.unop := by
    apply transport_map R g hc eY eY'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact CoefficientShift.cycles R g K ι hK hK' n 0 α
  have hd := IntegralComparison.Ext.CoefficientNaturality.short_homology R g (Augmented.ResolutionCycles.differentialSequence K (n + 1))
    (Augmented.ResolutionCycles.successiveSequence K n).f (Augmented.ResolutionCycles.successiveSequence K n).zero
    (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (hc ▸ eY').toModuleIso.hom) hd).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          (Contravariant.ResolutionHomologyData.homologyIso R Y (Augmented.ResolutionCycles.differentialSequence K (n + 1))
            (Augmented.ResolutionCycles.successiveSequence K n).f (Augmented.ResolutionCycles.successiveSequence K n).zero
            (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)).hom ≫ a) hs).trans
              (Category.assoc _ _ _).symm)))

theorem short (n : ℕ) : ShortComplex.homologyMap (IntegralComparison.Ext.CoefficientNaturality.shortMap R g 0 (Augmented.ResolutionCycles.differentialSequence K n)) ≫
    (Contravariant.Resolution.Comparison.shortHomologyIso R Y' K ι hK' n).hom =
      (Contravariant.Resolution.Comparison.shortHomologyIso R Y K ι hK n).hom ≫
        IntegralComparison.Ext.CoefficientNaturality.component R g (n + 1) Z.unop := by
  cases n with
  | zero => exact short_zero R g K ι hK hK'
  | succ n => exact short_succ R g K ι hK hK' n

theorem positive (n : ℕ) : HomologicalComplex.homologyMap (IntegralComparison.Ext.CoefficientNaturality.complexMap R g K) (n + 1) ≫
    (Contravariant.Resolution.Comparison.positiveHomologyIso R Y' K ι hK' n).hom =
      (Contravariant.Resolution.Comparison.positiveHomologyIso R Y K ι hK n).hom ≫
        IntegralComparison.Ext.CoefficientNaturality.component R g (n + 1) Z.unop := by
  have h₁ := Cochain.HomologyTripleNaturality.naturality (IntegralComparison.Ext.CoefficientNaturality.complexMap R g K) n
  have h₂ := short R g K ι hK hK' n
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (Contravariant.Resolution.Comparison.shortHomologyIso R Y' K ι hK' n).hom) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          ((Contravariant.Resolution.Comparison.complex R Y K).homologyIsoSc' n (n + 1) (n + 2)
            (by simp) (by simp)).hom ≫ a) h₂).trans (Category.assoc _ _ _).symm)))

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y' 0
local notation "aY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero.augmentation R Y K ι
local notation "aY'" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero.augmentation R Y' K ι
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.CoefficientNaturality.component R g 0 Z.unop

omit [QuasiIso ι] in
theorem augmentation : aY ≫ IntegralComparison.Ext.CoefficientNaturality.complexMap R g K = (CochainComplex.single₀ _).map η ≫ aY' := by
  apply HomologicalComplex.from_single_hom_ext
  change (aY).f 0 ≫ (IntegralComparison.Ext.CoefficientNaturality.complexMap R g K).f 0 =
    ((CochainComplex.single₀ _).map η).f 0 ≫ (aY').f 0
  rw [Contravariant.ResolutionZero.augmentation_zero,
    Contravariant.ResolutionZero.augmentation_zero, CochainComplex.single₀_map_f_zero]
  exact IntegralComparison.Ext.CoefficientNaturality.naturality R g 0 (Augmented.ResolutionCycles.augmentation K ι)

theorem zero : HomologicalComplex.homologyMap (IntegralComparison.Ext.CoefficientNaturality.complexMap R g K) 0 ≫
    (Contravariant.ResolutionZero.homologyIso R Y' K ι).hom =
      (Contravariant.ResolutionZero.homologyIso R Y K ι).hom ≫ η := by
  have h : HomologicalComplex.homologyMap aY 0 ≫ HomologicalComplex.homologyMap (IntegralComparison.Ext.CoefficientNaturality.complexMap R g K) 0 =
      HomologicalComplex.homologyMap ((CochainComplex.single₀ _).map η) 0 ≫
        HomologicalComplex.homologyMap aY' 0 :=
    (HomologicalComplex.homologyMap_comp aY (IntegralComparison.Ext.CoefficientNaturality.complexMap R g K) 0).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f 0) (augmentation R g K ι)).trans
        (HomologicalComplex.homologyMap_comp _ _ 0))
  exact comparison_square (isoOfQuasiIsoAt aY 0) (isoOfQuasiIsoAt aY' 0)
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 ((F).obj Z))
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 ((G).obj Z))
    (HomologicalComplex.homologyMap (IntegralComparison.Ext.CoefficientNaturality.complexMap R g K) 0)
    (HomologicalComplex.homologyMap ((CochainComplex.single₀ _).map η) 0) η h
    (HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℕ) 0 η)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (IntegralComparison.Ext.CoefficientNaturality.complexMap R g K) i ≫
    (Contravariant.ResolutionCohomology.homologyIso R Y' K ι hK' i).hom =
      (Contravariant.ResolutionCohomology.homologyIso R Y K ι hK i).hom ≫
        IntegralComparison.Ext.CoefficientNaturality.component R g i Z.unop := by
  cases i with
  | zero => exact CoefficientNaturality.zero R g K ι
  | succ n => exact positive R g K ι hK hK' n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CoefficientNaturality
