import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.UnitParameter
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization

/-! # Deformation One Uniqueness -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DeformationOneUniqueness.BundleCycles

noncomputable section

/-! Morphisms into the actual affine deformation at parameter one are
uniquely determined by their projection to the coefficient spectrum. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] (I : Ideal R)

def affineDeformationCoefficientProjection : Deformation.ClosedSupport.BundleCycles.affineDeformation I ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I)))

theorem affineDeformationOne_hom_ext {T : Scheme.{0}} (f g : T ⟶ Deformation.ClosedSupport.BundleCycles.affineDeformation I)
    (hc : f ≫ affineDeformationCoefficientProjection I = g ≫ affineDeformationCoefficientProjection I)
    (hf : f.appTop (Specialization.BundleCycles.affineDeformationParameterSection I) = 1)
    (hg : g.appTop (Specialization.BundleCycles.affineDeformationParameterSection I) = 1) : f = g := by
  let φ : Deformation.Iff.BundleCycles.deformationAlgebra I →+* Γ(T, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).inv ≫ f.appTop).hom
  let ψ : Deformation.Iff.BundleCycles.deformationAlgebra I →+* Γ(T, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).inv ≫ g.appTop).hom
  have hcoeff : φ.comp (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I)) =
      ψ.comp (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I)) := by
    let a : CommRingCat.of R ⟶ CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
      CommRingCat.ofHom (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I))
    have hn := Scheme.ΓSpecIso_inv_naturality a
    have hfg := congrArg (fun k : T ⟶ Spec (.of R) => (Scheme.ΓSpecIso (.of R)).inv ≫ k.appTop) hc
    change (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map a).appTop ≫ f.appTop =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map a).appTop ≫ g.appTop at hfg
    ext r
    have hr := ConcreteCategory.congr_hom hn r
    exact (congrArg (fun s => f.appTop s) hr).trans
      ((ConcreteCategory.congr_hom hfg r).trans (congrArg (fun s => g.appTop s) hr).symm)
  have hφ : φ (Deformation.Iff.BundleCycles.deformationParameter I) = 1 := hf
  have hψ : ψ (Deformation.Iff.BundleCycles.deformationParameter I) = 1 := hg
  apply ext_to_Spec
  exact CommRingCat.hom_ext (Deformation.UnitParameter.BundleCycles.deformationRingHom_eq_at_one I φ ψ hcoeff hφ hψ)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DeformationOneUniqueness.BundleCycles
