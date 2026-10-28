import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.CechLift
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech

/-! # Section Lifting -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SectionLifting.CrystallineSectionLifting

noncomputable section

/-!
# Surjectivity on sections from vanishing of first Čech cohomology

For a short exact sequence of native sheaves, local lifts of a section
form a zero-cochain. Exactness in degree one of the kernel's Čech complex
corrects it to a cocycle. Native degree-zero gluing then supplies a global
lift. The criterion applies to every actual frame-resolution term.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

theorem surjective (S : ShortComplex (Sheaf J V)) (hS : S.ShortExact)
    (hA : ∀ (t : Finset Q.thickening.ring), Ideal.span (t : Set Q.thickening.ring) = ⊤ →
      ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q (fun s : t => s.val)).obj S.X₁).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op Q)) := by
  have := hS.mono_f
  have := hS.epi_g
  intro x
  obtain ⟨t, ht, hl⟩ := LocalLifts.CrystallineLocalLifts.exists_principal_lifts p k X S.g Q x
  let s : t → Q.thickening.ring := fun i => i.val
  have hs : Ideal.span (Set.range s) = ⊤ := by
    simpa only [s, Subtype.range_coe_subtype, Finset.setOfPred_mem] using ht
  let y := fun i : t => (hl i).choose
  have hy := fun i : t => (hl i).choose_spec
  let z := CrystallineCech.CechLift.CrystallineCechLift.assemble p k X Q s S.X₂ y
  let C := CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s
  let a := SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation p k X Q s
  have hz : (C.map S.g).f 0 z = (a S.X₃).f 0 x :=
    CrystallineCech.CechLift.CrystallineCechLift.map_assemble p k X Q s S.g x y hy
  have hdz : (C.map S.g).f 1 ((C.obj S.X₂).d 0 1 z) = 0 := by
    have hc := congrArg (fun f => f z) ((C.map S.g).comm 0 1)
    have ha := congrArg (fun f => f x)
      (SheafCechAugmentation.CrystallineSheafCechAugmentation.restriction_cocycle p k X Q s S.X₃)
    exact hc.symm.trans ((congrArg ((C.obj S.X₃).d 0 1) hz).trans ha)
  obtain ⟨z', hz', hg⟩ := CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.exists_corrected_cycle
    p k X Q s S hS.exact 0 (hA t ht) z hdz
  obtain ⟨x', hx'⟩ := CrystallineCech.Gluing.CrystallineCechGluing.exists_augmentation p k X Q s S.X₂ hs z' hz'
  refine ⟨x', CrystallineCech.DegreeZero.CrystallineCechDegreeZero.augmentation_injective p k X Q s S.X₃ hs ?_⟩
  have hn := congrArg (fun f => f.f 0 x')
    (SheafCechAugmentation.CrystallineSheafCechAugmentation.augmentation_natural p k X Q s S.g)
  exact hn.trans ((congrArg ((C.map S.g).f 0) hx').trans (hg.trans hz))

theorem epi (S : ShortComplex (Sheaf J V)) (hS : S.ShortExact)
    (hA : ∀ (t : Finset Q.thickening.ring), Ideal.span (t : Set Q.thickening.ring) = ⊤ →
      ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q (fun s : t => s.val)).obj S.X₁).ExactAt 1) :
    Epi (S.g.hom.app (op Q)) :=
  (ModuleCat.epi_iff_surjective _).mpr (surjective p k X Q S hS hA)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SectionLifting.CrystallineSectionLifting
