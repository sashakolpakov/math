import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Invariant
import Mathlib.RingTheory.Flat.Equalizer

/-! # Line Module Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineModuleDescent.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: effective descent of line modules over arbitrary rings

Finite presentation descends by descending the kernel of a finite free
presentation. Thus line descent requires no noetherian hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open TensorProduct
open scoped TensorProduct

universe u

/-- Finite presentation descends along every faithfully flat ring map. -/
theorem finitePresentation_of_faithfullyFlat_baseChange
    (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S]
    [Module.FinitePresentation S (S ⊗[R] M)] : Module.FinitePresentation R M := by
  have : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let g := AlgebraTensorModule.lTensor S S f
  have hg : Function.Surjective g := LinearMap.lTensor_surjective S hf
  have : Module.Finite S (LinearMap.ker g) := .of_fg (Module.FinitePresentation.fg_ker g hg)
  have : Module.Finite S (S ⊗[R] LinearMap.ker f) :=
    Module.Finite.equiv (LinearMap.tensorKerEquiv S S f).symm
  have : Module.Finite R (LinearMap.ker f) := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  exact Module.finitePresentation_of_free_of_surjective f hf (Module.Finite.iff_fg.mp inferInstance)

/-- Invertibility of a line module descends without a finite-presentation
assumption: finite presentation is itself a consequence of faithful flatness. -/
theorem invertible_of_faithfullyFlat_baseChange
    (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S]
    [Module.Invertible S (S ⊗[R] M)] : Module.Invertible R M := by
  have : Module.FinitePresentation S (S ⊗[R] M) :=
    Module.finitePresentation_of_projective S (S ⊗[R] M)
  have := finitePresentation_of_faithfullyFlat_baseChange R S M
  exact Picard.PoincareBundle.Affine.LineDescent.invertible_of_faithfullyFlat_baseChange R S M

/-- The module constructed by effective descent of a line coaction is
invertible over an arbitrary base ring. -/
theorem descendedModule_invertible {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat) (D : Picard.PoincareBundle.Affine.Descent.ModuleDatum f)
    [Module.Invertible S D.A] : Module.Invertible R (Picard.PoincareBundle.Affine.Descent.descendedModule f hf D) := by
  let : Algebra R S := f.toAlgebra
  have : Module.FaithfullyFlat R S := hf
  have : Module.Invertible S (S ⊗[R] Picard.PoincareBundle.Affine.Descent.descendedModule f hf D) :=
    Module.Invertible.congr (Picard.PoincareBundle.Affine.Descent.baseChangeIso f hf D).symm.toLinearEquiv
  exact invertible_of_faithfullyFlat_baseChange R S (Picard.PoincareBundle.Affine.Descent.descendedModule f hf D)

/-- Geometric invariants of an actual line-bundle coaction form an
actual line bundle on every affine base. -/
theorem invariantSheaf_isLine {R S : CommRingCat.{u}} (f : R ⟶ S)
    (D : Picard.PoincareBundle.BeckDescent.SheafDatum (Spec.map f)) (hf : f.hom.FaithfullyFlat)
    (hD : Picard.PoincareBundle.Line.Bundles.IsLine D.A) :
    Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.BeckDescent.invariantSheaf (Spec.map f) D) := by
  have : D.A.IsQuasicoherent := Picard.PoincareBundle.QuasiCoherent.isQuasicoherent_of_isLine D.A hD
  let M := (moduleSpecΓFunctor (R := R)).obj (Picard.PoincareBundle.BeckDescent.invariantSheaf (Spec.map f) D)
  have hExt : Module.Invertible S ((ModuleCat.extendScalars f.hom).obj M) :=
    Picard.PoincareBundle.Affine.Classification.invertible_of_isLine_tilde _
      (hD.of_iso (Picard.PoincareBundle.Affine.Invariant.extendedInvariantTildeIso f D hf.flat).symm)
  let : Algebra R S := f.hom.toAlgebra
  have : Module.FaithfullyFlat R S := hf
  have : Module.Invertible S (S ⊗[R] M) := hExt
  have : Module.Invertible R M := invertible_of_faithfullyFlat_baseChange R S M
  exact (Picard.PoincareBundle.TildePullback.isLine_tilde_of_invertible M).of_iso (Picard.PoincareBundle.Affine.Invariant.invariantTildeIso f D)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineModuleDescent.Construction.LineDescent
