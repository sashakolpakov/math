import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.SheafLocalLifts
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.DegreeZero
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechLift

/-! # Section Lifting -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.SectionLifting.AffineSectionLifting

noncomputable section

/-! Vanishing of first principal Čech cohomology of the kernel makes an actual epimorphism of affine sheaves surjective on global sections. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (A : CommRingCat) (g : Spec A ⟶ Spec (CommRingCat.of R))

local notation "X" => Over.mk g
local notation "J" => Opens.grothendieckTopology (Spec (A))

theorem surjective (S : ShortComplex (Sheaf J (ModuleCat R))) (hS : S.ShortExact)
    (hA : ∀ t : Finset A, Ideal.span (t : Set A) = ⊤ →
      ((Cech.CechSheaf.functor R X (fun a : t => PrimeSpectrum.basicOpen a.val)).obj S.X₁).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  have := hS.mono_f
  have := hS.epi_g
  intro x
  obtain ⟨t, ht, hl⟩ := SheafLocalLifts.AffineSheafLocalLifts.exists_principal_lifts R (A) S.g x
  let U : t → (Spec (A)).Opens := fun a => PrimeSpectrum.basicOpen a.val
  have hU : iSup U = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using ht
  let y := fun a : t => (hl a).choose
  have hy := fun a : t => (hl a).choose_spec
  let C := Cech.CechSheaf.functor R X U
  let z := Cech.CechLift.assemble R X U S.X₂.obj y
  have hz : (C.map S.g).f 0 z = (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U S.X₃.obj).f 0 x :=
    Cech.CechLift.map_assemble R X U S.g.hom x y hy
  have ha : (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U S.X₃.obj).f 0 ≫
      (C.obj S.X₃).d 0 1 = 0 :=
    (congrArg (fun f => f ≫ (C.obj S.X₃).d 0 1)
      (Cech.CechLift.augmentation_f_zero R X U S.X₃.obj)).trans
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.restriction_cocycle R X U S.X₃.obj)
  have hdz : (C.map S.g).f 1 ((C.obj S.X₂).d 0 1 z) = 0 :=
    (congrArg (fun f => f z) ((C.map S.g).comm 0 1)).symm.trans
      ((congrArg ((C.obj S.X₃).d 0 1) hz).trans (congrArg (fun f => f x) ha))
  obtain ⟨z', hz', hg⟩ := Cech.CechSheaf.exists_corrected_cycle R X U S hS.exact 0 (hA t ht) z hdz
  obtain ⟨x', hx'⟩ := Cech.DegreeZero.CechDegreeZero.exists_augmentation R X S.X₂ U hU z' hz'
  refine ⟨x', ?_⟩
  apply Cech.DegreeZero.CechDegreeZero.augmentation_injective R X S.X₃ U hU
  have hn := congrArg (fun f => f.f 0 x')
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation_natural R X U S.g.hom)
  exact hn.trans ((congrArg ((C.map S.g).f 0) hx').trans (hg.trans hz))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.SectionLifting.AffineSectionLifting
