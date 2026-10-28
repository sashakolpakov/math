/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealInvertible

/-! # Canonical Ideal Frame -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalIdealFrame

noncomputable section

/-! Canonical trivializations of principal kernel ideals. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U)

def localIdealElement : Γ(IdealModule.idealModule f, U.1) :=
  (IdealModule.idealModuleAppIdealIso f U).inv ⟨r, hr⟩

@[simp]
theorem idealModuleAppIdealIso_hom_localIdealElement :
    (IdealModule.idealModuleAppIdealIso f U).hom (localIdealElement f U r hr) = ⟨r, hr⟩ :=
  Iso.inv_hom_id_apply _ _

def localIdealGeneratorHom :
    Invertible.Scheme.Modules.unitObj U.1.toScheme ⟶ (IdealModule.idealModule f).restrict U.1.ι :=
  CanonicalAffineFrame.openGeneratorHom (IdealModule.idealModule f) U.1 (localIdealElement f U r hr)

theorem localIdealElement_smul_bijective
    (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    Function.Bijective (fun a : Γ(Y, U.1) => a • localIdealElement f U r hr) := by
  let e := IdealModule.idealModuleAppIdealIso f U
  have he := ConcreteCategory.bijective_of_isIso e.hom
  have hformula (a : Γ(Y, U.1)) :
      (e.hom (a • localIdealElement f U r hr) : Γ(Y, U.1)) = a * r := by
    rw [e.hom.hom.map_smul]
    change (a • (IdealModule.idealModuleAppIdealIso f U).hom (localIdealElement f U r hr) :
      f.ker.ideal U).val = _
    rw [idealModuleAppIdealIso_hom_localIdealElement]
    rfl
  constructor
  · intro a b hab
    have h := congrArg (fun x => (e.hom x : Γ(Y, U.1))) hab
    rw [hformula, hformula] at h
    exact (mul_cancel_right_mem_nonZeroDivisors hnzd).mp h
  · intro y
    have hy : (e.hom y : Γ(Y, U.1)) ∈ Ideal.span {r} := by
      rw [← hspan]
      exact (e.hom y).property
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
    refine ⟨a, he.1 ?_⟩
    apply Subtype.ext
    rw [hformula]
    exact ha

theorem isIso_localIdealGeneratorHom [IsAffineHom f]
    (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    IsIso (localIdealGeneratorHom f U r hr) := by
  have : (IdealModule.idealModule f).IsQuasicoherent := IdealModule.idealModule_quasicoherent f
  exact CanonicalAffineFrame.openGeneratorHom_isIso (IdealModule.idealModule f) U.1 U.2 _
    (localIdealElement_smul_bijective f U r hr hspan hnzd)

def localIdealGeneratorIso [IsAffineHom f]
    (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    Invertible.Scheme.Modules.unitObj U.1.toScheme ≅ (IdealModule.idealModule f).restrict U.1.ι := by
  letI := isIso_localIdealGeneratorHom f U r hr hspan hnzd
  exact asIso (localIdealGeneratorHom f U r hr)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalIdealFrame
