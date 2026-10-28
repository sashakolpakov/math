import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingFunctor

/-! # Conjugate Ring Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.ConjugateRingMap.CrystallineConjugateRingMap

noncomputable section

/-! The underlying ring map of a frame restriction transported through algebra isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  {F G : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : G ⟶ F)
  {A C : CommAlgCat.{u} B}
  (eF : A ≅ (FrameRingFunctor.CrystallineFrameRingFunctor.bounded f n).obj (op F))
  (eG : C ≅ (FrameRingFunctor.CrystallineFrameRingFunctor.bounded f n).obj (op G))

theorem ringHom :
    ((eF.hom ≫ (FrameRingFunctor.CrystallineFrameRingFunctor.bounded f n).map α.op ≫ eG.inv).hom.toRingHom) =
      eG.inv.hom.toRingHom.comp (α.hom.ringMap.toRingHom.comp eF.hom.hom.toRingHom) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.ConjugateRingMap.CrystallineConjugateRingMap
