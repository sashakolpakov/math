import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EffectiveAlbaneseDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HodgeComparisonCapstone
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Total

/-! # Albanese -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Albanese

noncomputable section

/-! Apply the proved HodgeComparison comparison to the actual arithmetic Albanese map.
The comparison concerns its native scalar extension and exact pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {R : Type} [Field R] [NumberField R] [Algebra R ℂ]

def complexSourceVariety (X : Over (Spec (.of R)))
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom) :
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := by
  let F : Over (Spec (.of R)) ⥤ Over (Spec (.of ℂ)) :=
    Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  have hSmooth : Smooth (F.obj X).hom := inferInstanceAs
    (Smooth (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))))
  have : IsProper (F.obj X).hom := inferInstanceAs
    (IsProper (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))))
  have : GeometricallyConnected (F.obj X).hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))))
  have hConnected : ConnectedSpace (F.obj X).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (F.obj X).hom
  have hCompact : QuasiCompact (F.obj X).hom := inferInstance
  exact ⟨AlbaneseArithmeticIsogeny.complexSourcePresentation X P,
    @ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral ℂ inferInstance (F.obj X).left
      (F.obj X).hom hSmooth hCompact hConnected⟩

theorem arithmetic_albanese_h1_of_exact_comparison
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A.toOver)
    (ha : Albanese.IsAlbaneseMap (AlbaneseArithmeticIsogeny.complexSourcePresentation X P)
      (Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀) A a)
    (B : Base.ArithmeticBaseExtension R (algebraMap R ℂ))
    (Y : Over (Spec (.of B.extension.carrier)))
    (r : (Over.pullback B.fieldExtension).obj X ⟶ Y)
    (eX : (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj
        ((Over.pullback B.fieldExtension).obj X) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X)
    (eY : (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj Y ≅ A.toOver)
    (hr : (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).map r ≫ eY.hom =
      eX.hom ≫ a) :
    Function.Bijective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
      ((Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).map r)).hom := by
  have hA := Total.albanese_h1_bijective HodgeComparisonCapstone.provedHodgeComparisonInput (complexSourceVariety X P)
    (Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀) A a ha
  exact Total.betti_bijective_of_iso_comp _ a eX eY hr 1 hA

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Albanese
