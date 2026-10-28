import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ArithmeticAlbanese
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseTransfer

/-! # Albanese Components -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Package the constructed common-field Albanese realizations as IntegralModel's
actual component data and transfer their complex universal properties. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [Field R] [NumberField R] [Algebra R ℂ] {r : ℕ}
    {X : Fin r → Over (Spec (.of R))} {x₀ : ∀ i, 𝟙_ (Over (Spec (.of R))) ⟶ X i}
    {A : Fin r → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    {a : ∀ i, (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj (X i) ⟶ (A i).toOver}
    (D : Finite.ArithmeticAlbanese.FiniteArithmeticAlbaneseRealization X x₀ A a)

def Finite.ArithmeticAlbanese.FiniteArithmeticAlbaneseRealization.componentData
    (T : Over (Spec (.of D.base.extension.carrier))) : Components.ComponentAlbaneseData T r where
  S i := (Over.pullback D.base.fieldExtension).obj (X i)
  A i := { X := (D.model i).toOver }
  x₀ i := Section.Comparisons.mappedSection (Over.pullback D.base.fieldExtension) (x₀ i)
  a i := D.map i

theorem Finite.ArithmeticAlbanese.FiniteArithmeticAlbaneseRealization.componentData_isComplexAlbanese
    [∀ i, Smooth (X i).hom] [∀ i, IsProper (X i).hom] [∀ i, GeometricallyConnected (X i).hom]
    (T : Over (Spec (.of D.base.extension.carrier)))
    (P : ∀ i, Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj (X i)).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj (X i)).hom)
    (hA : ∀ i, Albanese.IsAlbaneseMap (AlbaneseArithmeticIsogeny.complexSourcePresentation (X i) (P i))
      (Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) (x₀ i)) (A i) (a i))
    (i : Fin r) :
    (D.componentData T).IsComplexAlbanese (Spec.map (CommRingCat.ofHom D.base.embedding)) i := by
  let C := D.componentData T
  let β := Spec.map (CommRingCat.ofHom D.base.embedding)
  let V := Arithmetic.Albanese.complexSourceVariety (X i) (P i)
  let eX : C.complexSurface β i ≅ V.toOver := D.sourceIso i
  let eA : (C.complexAbelian β i).X ≅ (A i).toOver := D.targetIso i
  have : IsMonHom eA.hom := D.groupComparison i
  exact Components.ComponentAlbaneseData.isComplexAlbanese_of_fiber_iso C β i V (A i) eX eA
    (Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) (x₀ i))
    (a i) (D.sourcePoint i) (D.comparison i) (hA i)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
