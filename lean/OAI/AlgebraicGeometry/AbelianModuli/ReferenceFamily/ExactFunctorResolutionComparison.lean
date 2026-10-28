import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage

/-! # Exact Functor Resolution Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactFunctorResolutionComparison

noncomputable section

/-! Exact inverse image of an actual injective resolution admits a
constructed comparison to any target injective resolution. Its degree-zero
square retains the original coefficient morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [EnoughInjectives D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A : C} {B : D} (I : InjectiveResolution A) (J : InjectiveResolution B)
    (a : F.obj A ⟶ B)

def exactFunctorResolutionComparison :
    (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ J.cocomplex :=
  Comparison.Betti.ResolutionExactImage.toInjective
      (Comparison.Betti.ResolutionExactImage.exactImage (Comparison.Betti.ResolutionExactImage.ofInjective I) F)
      (injectiveResolution (F.obj A)) ≫
    InjectiveResolution.desc a J (injectiveResolution (F.obj A))

theorem exactFunctorResolutionComparison_zero :
    F.map (I.ι.f 0) ≫ (exactFunctorResolutionComparison F I J a).f 0 = a ≫ J.ι.f 0 := by
  let R := Comparison.Betti.ResolutionExactImage.exactImage (Comparison.Betti.ResolutionExactImage.ofInjective I) F
  let K := injectiveResolution (F.obj A)
  have h : F.map (I.ι.f 0) ≫ (Comparison.Betti.ResolutionExactImage.toInjective R K).f 0 = K.ι.f 0 := by
    exact Comparison.Betti.ResolutionExactImage.augmentation_zeroMap R K
  change F.map (I.ι.f 0) ≫
    ((Comparison.Betti.ResolutionExactImage.toInjective R K).f 0 ≫ (InjectiveResolution.desc a J K).f 0) = _
  exact (Category.assoc (F.map (I.ι.f 0)) ((Comparison.Betti.ResolutionExactImage.toInjective R K).f 0)
    ((InjectiveResolution.desc a J K).f 0)).symm.trans
      ((congrArg (fun t => t ≫ (InjectiveResolution.desc a J K).f 0) h).trans
        (InjectiveResolution.desc_commutes_zero a J K))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactFunctorResolutionComparison
