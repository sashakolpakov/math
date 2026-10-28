import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeGraphPolynomials
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BoundedEndomorphismDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter

/-! # Projective Endomorphism Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ProjectiveEndomorphismDescent

noncomputable section

/-! The full Presentations inputs and proved rigidity descend every finite tuple of
complex endomorphisms of a specified projective arithmetic abelian model.
The graph-polynomial conditions are established from the actual maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem projective_endomorphism_tuple_descends
    (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    {g n : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.scheme)
    (V : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : V.toOver ≅ (A.pullback (Spec.map (CommRingCat.ofHom κ))).scheme)
    [IsMonHom e.hom]
    (r : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback (Spec.map (CommRingCat.ofHom κ)))) :
    ∃ (F : IntegralModel.Base.ArithmeticBaseExtension K κ)
      (rF : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback F.fieldExtension)),
      F.denominator = 1 ∧ ∀ i, IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrict A F.complexFieldMap (rF i) = r i := by
  classical
  let t := Spec.map (CommRingCat.ofHom κ)
  let f (i : Fin n) := IntegralModel.EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (Over.mk t) ((r i).hom _)
  have hpol (i : Fin n) := RelativeGraphPolynomials.exists_relative_morphism_graph_polynomial
    hHilb A.scheme BA t (f i)
  choose P hP using hpol
  obtain ⟨B, L, hB, ⟨M⟩⟩ := hEnd A.scheme BA n P []
  exact BoundedEndomorphismDescent.e34_bounded_endomorphism_tuple_descends κ A M V e r (fun i => hP i B hB)

theorem projective_endomorphism_tuple_descends_native
    (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    {g n : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.scheme)
    (r : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback (Spec.map (CommRingCat.ofHom κ)))) :
    ∃ (F : IntegralModel.Base.ArithmeticBaseExtension K κ)
      (rF : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback F.fieldExtension)),
      F.denominator = 1 ∧ ∀ i, IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrict A F.complexFieldMap (rF i) = r i := by
  let AC := A.pullback (Spec.map (CommRingCat.ofHom κ))
  let BC := (IntegralModel.Presentations.Parameter.nativeProjectivePresentationOfPresentations BA).baseChange (Spec.map (CommRingCat.ofHom κ))
  let PC := AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation BC
  let : IsMonHom (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso AC PC).hom :=
    AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso_isMonHom AC PC
  exact projective_endomorphism_tuple_descends hHilb hEnd κ A BA
    (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native AC PC) (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso AC PC) r

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ProjectiveEndomorphismDescent
