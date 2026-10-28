import OAI.AlgebraicGeometry.Comparison.Betti.AcyclicHomQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomologyExt

/-! # Resolution Ext Calculation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionExtCalculation

noncomputable section

/-! The actual Hom complex of a proved acyclic resolution computes Ext
through its augmentation-preserving map to an injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite _root_.HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C] [HasExt.{w} C]
  {R : Type v} [CommRing R] [Linear R C]
  (A : C) {F : C} (D : ResolutionExactImage.Data F)

def acyclicResolutionHomologyExtEquiv
    (hExt : ∀ p q, Subsingleton (Ext A (D.complex.X p) (q + 1))) (n : ℕ) :
    ((((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℕ)).obj D.complex).homology n ≃ₗ[R]
      Ext A F n := by
  let I := injectiveResolution F
  let f := ResolutionExactImage.toInjective D I
  have hf : QuasiIso f := ResolutionExactImage.toInjective_quasiIso D I
  let H := ((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℕ)
  have hH : QuasiIso (H.map f) := AcyclicHomQuasiIso.Ext.nonnegativeLinearHomComplex_map_quasiIso A f hExt
    (fun p q => Ext.subsingleton_of_injective A (I.cocomplex.X p) q)
  exact (isoOfQuasiIsoAt (H.map f) n).toLinearEquiv.trans
    (InjectiveHomologyExt.homologyExtLinearEquiv (R := R) (X := A) I n)

theorem acyclicResolution_ext_vanish
    (hExt : ∀ p q, Subsingleton (Ext A (D.complex.X p) (q + 1)))
    (hHom : ∀ q, ((((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℕ)).obj
      D.complex).ExactAt (q + 1)) (q : ℕ) : Subsingleton (Ext A F (q + 1)) := by
  have : Subsingleton
      (((((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℕ)).obj
        D.complex).homology (q + 1)) := ModuleCat.subsingleton_of_isZero (hHom q).isZero_homology
  exact (acyclicResolutionHomologyExtEquiv (R := R) A D hExt (q + 1)).symm.injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionExtCalculation
