import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CrystallineCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FrameForms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation

/-! # Finite Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.FiniteFrame

noncomputable section

/-!
# IntegralComparison: finite crystalline frames over affine opens of a scheme

Postcomposing the prescribed closed fibre with an actual affine open
immersion produces a finite frame in the original global crystalline
site. Every small thickening whose closed map lands in this open maps
to one of these frames, and its ambient forms retain their finiteness.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] (x : σ → C)
  (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] C))
  (X : Over (Spec (CommRingCat.of k)))
  (j : (Crystalline.Presentation.affineScheme k C).left ⟶ X.left) [IsOpenImmersion j]
  (hj : j ≫ X.hom = (Crystalline.Presentation.affineScheme k C).hom)

/-- The finite affine frame, as an object of the original global crystalline site. -/
def frame (n : ℕ) : Witt.Crystalline.CrystallineObject p k X where
  ring := (IntegralComparison.Finite.CrystallineFrame.object p k C σ x n hx).ring
  base := (IntegralComparison.Finite.CrystallineFrame.object p k C σ x n hx).base
  ideal := (IntegralComparison.Finite.CrystallineFrame.object p k C σ x n hx).ideal
  dividedPowers := (IntegralComparison.Finite.CrystallineFrame.object p k C σ x n hx).dividedPowers
  baseCompatible := (IntegralComparison.Finite.CrystallineFrame.object p k C σ x n hx).baseCompatible
  primeNilpotent := (IntegralComparison.Finite.CrystallineFrame.object p k C σ x n hx).primeNilpotent
  nilIdeal := (IntegralComparison.Finite.CrystallineFrame.object p k C σ x n hx).nilIdeal
  openMap := (IntegralComparison.Finite.CrystallineFrame.object p k C σ x n hx).openMap ≫ j
  overBase := by
    rw [Category.assoc, Crystalline.OpenPresentation.overWitt p k C X j hj]
    exact (IntegralComparison.Finite.CrystallineFrame.object p k C σ x n hx).overBase

variable (U : Witt.Crystalline.CrystallineObject p k X)
  (closedFactor : Spec (CommRingCat.of (U.ring ⧸ U.ideal)) ⟶ (Crystalline.Presentation.affineScheme k C).left)
  (ht : closedFactor ≫ j = U.openMap)

def affineObject : Witt.Crystalline.CrystallineObject p k (Crystalline.Presentation.affineScheme k C) where
  ring := U.ring
  base := U.base
  ideal := U.ideal
  dividedPowers := U.dividedPowers
  baseCompatible := U.baseCompatible
  primeNilpotent := U.primeNilpotent
  nilIdeal := U.nilIdeal
  openMap := closedFactor
  isOpenImmersion := by
    have : IsOpenImmersion (closedFactor ≫ j) := by rw [ht]; infer_instance
    exact IsOpenImmersion.of_comp closedFactor j
  overBase := by
    rw [← Crystalline.OpenPresentation.overWitt p k C X j hj, ← Category.assoc, ht]
    exact U.overBase

def presentationMorphism : U ⟶ frame p k C σ x hx X j hj
    (Crystalline.Cover.levelBound p k C (affineObject p k C X j hj U closedFactor ht)) where
  ringMap := (IntegralComparison.Finite.CrystallineCover.presentationMorphism p k C σ x
    (affineObject p k C X j hj U closedFactor ht) hx).ringMap
  overBase := (IntegralComparison.Finite.CrystallineCover.presentationMorphism p k C σ x
    (affineObject p k C X j hj U closedFactor ht) hx).overBase
  overX := by
    let α := IntegralComparison.Finite.CrystallineCover.presentationMorphism p k C σ x
      (affineObject p k C X j hj U closedFactor ht) hx
    change Crystalline.Site.AffineThickening.quotientMap
      (affineObject p k C X j hj U closedFactor ht)
      (IntegralComparison.Finite.CrystallineFrame.object p k C σ x _ hx) α.ringMap |> fun q =>
        Spec.map (CommRingCat.ofHom q) ≫
          ((IntegralComparison.Finite.CrystallineFrame.object p k C σ x _ hx).openMap ≫ j) = U.openMap
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ j) α.overX).trans ht)

include ht in
theorem exists_presentation : ∃ n : ℕ, Nonempty (U ⟶ frame p k C σ x hx X j hj n) :=
  ⟨_, ⟨presentationMorphism p k C σ x hx X j hj U closedFactor ht⟩⟩

omit U closedFactor ht in
/-- The global frame's actual Witt-relative forms are finite over its ambient ring. -/
theorem forms_finite [Finite σ] (n m : ℕ) :
    let V := frame p k C σ x hx X j hj n
    letI : Algebra (WittVector p k) V.ring := V.base.toAlgebra
    Module.Finite V.ring
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form (WittVector p k) V.ring V.ideal V.dividedPowers m) :=
  IntegralComparison.Finite.FrameForms.object_forms_finite p k C σ x n hx m

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.FiniteFrame
