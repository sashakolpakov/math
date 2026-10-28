import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormAutomorphism

/-! # Homogeneous Localization Automorphism -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousLocalizationAutomorphism

noncomputable section

/-! An invertible change of homogeneous linear coordinates induces
an actual ring isomorphism on the corresponding degree-zero localizations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.HomogeneousLocalization OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis.GradedMap

theorem map_inverse {a b : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading a →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading b)
    (g : Foundations.Scheme.ProjectiveSpace.projectiveGrading b →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading a)
    {P : Submonoid (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing a)} {Q : Submonoid (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing b)}
    (hf : P ≤ Q.comap f) (hg : Q ≤ P.comap g) (hgf : ∀ r, g (f r) = r)
    (p : HomogeneousLocalization (Foundations.Scheme.ProjectiveSpace.projectiveGrading a) P) :
    HomogeneousLocalization.map g hg (HomogeneousLocalization.map f hf p) = p := by
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective p
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  congr 1
  · exact hgf _
  · apply Subtype.ext
    exact hgf _

variable {n : ℕ} (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
  (s : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)

theorem forward_powers : Submonoid.powers s ≤
    (Submonoid.powers (LinearFormBasis.GradedMap.gradedHom e.toLinearMap s)).comap (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) := by
  rintro _ ⟨k, rfl⟩
  exact ⟨k, (map_pow (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) s k).symm⟩

theorem backward_powers : Submonoid.powers (LinearFormBasis.GradedMap.gradedHom e.toLinearMap s) ≤
    (Submonoid.powers s).comap (LinearFormBasis.GradedMap.gradedHom e.symm.toLinearMap) := by
  rintro _ ⟨k, rfl⟩
  refine ⟨k, ?_⟩
  change s ^ k = LinearFormBasis.GradedMap.gradedHom e.symm.toLinearMap (LinearFormBasis.GradedMap.gradedHom e.toLinearMap s ^ k)
  rw [map_pow]
  have he : LinearFormBasis.GradedMap.gradedHom e.symm.toLinearMap (LinearFormBasis.GradedMap.gradedHom e.toLinearMap s) = s :=
    DFunLike.congr_fun (LinearFormAutomorphism.graded_inverse e.symm) s
  rw [he]

def backward : Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (LinearFormBasis.GradedMap.gradedHom e.toLinearMap s) →+* Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s :=
  HomogeneousLocalization.map (LinearFormBasis.GradedMap.gradedHom e.symm.toLinearMap) (backward_powers e s)

theorem backward_forward (p : Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s) :
    HomogeneousLocalizationAutomorphism.backward e s (Away.map (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) s p) = p :=
  map_inverse (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) (LinearFormBasis.GradedMap.gradedHom e.symm.toLinearMap) (forward_powers e s) (backward_powers e s)
    (fun r => DFunLike.congr_fun (LinearFormAutomorphism.graded_inverse e.symm) r) p

theorem forward_backward (p : Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (LinearFormBasis.GradedMap.gradedHom e.toLinearMap s)) :
    Away.map (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) s (HomogeneousLocalizationAutomorphism.backward e s p) = p :=
  map_inverse (LinearFormBasis.GradedMap.gradedHom e.symm.toLinearMap) (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) (backward_powers e s) (forward_powers e s)
    (fun r => DFunLike.congr_fun (LinearFormAutomorphism.graded_inverse e) r) p

def equivalence : Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s ≃+* Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (LinearFormBasis.GradedMap.gradedHom e.toLinearMap s) where
  __ := Away.map (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) s
  invFun := HomogeneousLocalizationAutomorphism.backward e s
  left_inv := backward_forward e s
  right_inv := forward_backward e s

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousLocalizationAutomorphism
