import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-! # Number Field Base Continuity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.NumberFieldBaseContinuity.Abelian

noncomputable section

/-!
An actual morphism from a complex scheme to a number-field spectrum has
locally constant complex embeddings on native points. This keeps the
arithmetic base embedding fixed when applying represented moduli data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
open scoped _root_.Topology Classical

section

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {K : Type} [CommRing K]

def schemeScalarValues (j : S.left ⟶ Spec (CommRingCat.of K))
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : K →+* ℂ := (Spec.preimage (s.left ≫ j)).hom

theorem schemeScalarValues_affine (j : S.left ⟶ Spec (CommRingCat.of K))
    (A : CommAlgCat ℂ) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ S) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (a : K) :
    schemeScalarValues j (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x) a =
      x ((Spec.preimage (i.left ≫ j)).hom a) := by
  let iA : Spec (CommRingCat.of A) ⟶ S.left := i.left
  let r : K →+* A := (Spec.preimage (i.left ≫ j)).hom
  have hmap : (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x).left ≫ j =
      Spec.map (CommRingCat.ofHom (x.toRingHom.comp r)) := by
    change ((AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A x).left ≫ i.left) ≫ j = _
    rw [AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
    change (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ iA) ≫ j = _
    rw [Category.assoc]
    have hr : Spec.map (CommRingCat.ofHom r) = iA ≫ j := Spec.map_preimage _
    rw [← hr, ← Spec.map_comp]
    rfl
  have hr : Spec.preimage ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x).left ≫ j) =
      CommRingCat.ofHom (x.toRingHom.comp r) := by
    apply Spec.map_injective
    rw [Spec.map_preimage]
    exact hmap
  exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of ℂ => f.hom a) hr

theorem continuous_schemeScalarValues (j : S.left ⟶ Spec (CommRingCat.of K)) :
    Continuous (fun s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S => (schemeScalarValues j s : K → ℂ)) := by
  apply continuous_pi
  intro a
  apply (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineTests _).mpr
  intro A i
  simp only [schemeScalarValues_affine]
  exact AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval _

end

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {K : Type} [Field K] [NumberField K]

theorem numberField_structure_locally_constant
    (j : S.left ⟶ Spec (CommRingCat.of K)) (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    ∀ᶠ s in 𝓝 s₀, s.left ≫ j = s₀.left ≫ j := by
  let v := fun s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S => (schemeScalarValues j s : K → ℂ)
  have hv : Continuous v := continuous_schemeScalarValues j
  have hfinite : (Set.range v).Finite :=
    (Set.finite_range (fun f : K →+* ℂ => (f : K → ℂ))).subset (by
      rintro f ⟨s, rfl⟩
      exact ⟨schemeScalarValues j s, rfl⟩)
  let bad := Set.range v \ {v s₀}
  have hbad : IsClosed bad := hfinite.sdiff.isClosed
  have havoid : ∀ᶠ s in 𝓝 s₀, v s ∉ bad :=
    hv.continuousAt.preimage_mem_nhds (hbad.isOpen_compl.mem_nhds (by simp [bad]))
  filter_upwards [havoid] with s hs
  have heq : v s = v s₀ := by
    by_contra hne
    exact hs ⟨⟨s, rfl⟩, hne⟩
  have hr : Spec.preimage (s.left ≫ j) = Spec.preimage (s₀.left ≫ j) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun a => congrFun heq a)
  exact (Spec.map_preimage (s.left ≫ j)).symm.trans
    ((congrArg Spec.map hr).trans (Spec.map_preimage (s₀.left ≫ j)))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.NumberFieldBaseContinuity.Abelian
