import OAI.AlgebraicGeometry.PELModuli.IntegralModel.TangentPointCoefficients
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has

/-! # Lie Characters -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieCharacters

noncomputable section

/-! The prescribed arithmetic CM characters are actual global functions
on the parameter scheme. Their values are the original base-field maps
appearing in IntegralModel's integral Lie-rank predicate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def arithmeticSectionCharacter {R B : Type} [CommRing R] [CommRing B]
    (M : Over (Spec (.of R))) (c : B →+* R) : B →+* Γ(M.left, ⊤) :=
  M.hom.appTop.hom.comp ((Scheme.ΓSpecIso (.of R)).inv.hom.comp c)

theorem arithmeticSectionCharacter_value {R B k : Type} [CommRing R] [CommRing B] [Field k]
    (M : Over (Spec (.of R))) (c : B →+* R) (p : Spec (.of k) ⟶ M.left)
    (j : R →+* k) (hp : p ≫ M.hom = Spec.map (CommRingCat.ofHom j)) :
    (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap p).comp (arithmeticSectionCharacter M c) = j.comp c := by
  have hn : (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom j)).appTop ≫
      (Scheme.ΓSpecIso (.of k)).hom = CommRingCat.ofHom j := by
    rw [Scheme.ΓSpecIso_naturality]
    exact (Scheme.ΓSpecIso (.of R)).inv_hom_id_assoc _
  ext b
  change HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap p (M.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv (c b))) = j (c b)
  have h := RingHom.congr_fun (TangentPointCoefficients.RelativeTangent.coefficientMap_postcomp p M.hom)
    ((Scheme.ΓSpecIso (.of R)).inv (c b))
  rw [hp] at h
  exact h.symm.trans (congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of k => f (c b)) hn)

def integralLieCharacter {E R : Type} [Field E] [Algebra ℚ E] [CommRing R]
    (M : Over (Spec (.of R))) (iotaO : NumberField.RingOfIntegers E →+* R)
    (τ : E ≃ₐ[ℚ] E) : NumberField.RingOfIntegers E →+* Γ(M.left, ⊤) :=
  arithmeticSectionCharacter M (iotaO.comp (NumberField.RingOfIntegers.mapRingHom τ.toRingHom))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieCharacters
