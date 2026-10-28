import OAI.AlgebraicGeometry.Resolution.Blowups.ReesProjectiveCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveProportionalMaps
import Mathlib.Analysis.Complex.Polynomial.Basic
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective

/-! # Rees Projective Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReesProjectiveComparison.Construction

noncomputable section

/-! Equality of local Rees projective maps from proportional center equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R S : Type} [CommRing R] [CommRing S]

@[simp]
theorem reesGradedMapTo_generator (I : Ideal R) (J : Ideal S)
    (φ : R →+* S) (h : I.map φ = J) (a : I) :
    Blowup.Functor.Construction.reesGradedMapTo I J φ h (Blowup.Charts.Construction.reesGenerator I a) =
      Blowup.Charts.Construction.reesGenerator J ⟨φ a.val, h ▸ Ideal.mem_map_of_mem φ a.property⟩ := by
  apply Subtype.ext
  exact Polynomial.map_monomial φ

@[simp]
theorem reesGradedMapTo_constants (I : Ideal R) (J : Ideal S)
    (φ : R →+* S) (h : I.map φ = J) (r : R) :
    Blowup.Functor.Construction.reesGradedMapTo I J φ h (algebraMap R (reesAlgebra I) r) =
      algebraMap S (reesAlgebra J) (φ r) := by
  apply Subtype.ext
  exact Polynomial.map_C φ

theorem reesProjectiveCoordinateMap_restriction_over (I : Ideal R) (J : Ideal S)
    (κR : ℂ →+* R) (κS : ℂ →+* S) (φ : R →+* S)
    (hκ : φ.comp κR = κS) (hI : I.map φ = J)
    {m : ℕ} (a : Fin (m + 1) → I) (hgen : Submodule.span R (Set.range a) = ⊤) :
    (Blowup.Functor.Construction.affineBlowupMapTo I J φ hI ≫ ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap I κR a hgen) ≫
      Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = ReesGrading.Construction.affineBlowupToSpec J ≫ Spec.map (CommRingCat.ofHom κS) := by
  rw [Category.assoc, ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap_over, ← Category.assoc,
    Blowup.Functor.Construction.affineBlowupMapTo_over, Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext hκ

variable {T : Type} [CommRing T]

/-- Two projective generator families give the same actual map on a
common reduced finite-type Rees blowup whenever their equations differ by a common unit. -/
theorem reesProjectiveCoordinateMap_common_unit
    (I : Ideal R) (J : Ideal S) (L : Ideal T)
    (κR : ℂ →+* R) (κS : ℂ →+* S) (κT : ℂ →+* T)
    (φ : R →+* T) (ψ : S →+* T)
    (hφκ : φ.comp κR = κT) (hψκ : ψ.comp κS = κT)
    (hI : I.map φ = L) (hJ : J.map ψ = L)
    {m : ℕ} (a : Fin (m + 1) → I) (b : Fin (m + 1) → J)
    (ha : Submodule.span R (Set.range a) = ⊤) (hb : Submodule.span S (Set.range b) = ⊤)
    [IsReduced (ReesGrading.Construction.affineBlowup L)]
    [LocallyOfFiniteType (ReesGrading.Construction.affineBlowupToSpec L ≫ Spec.map (CommRingCat.ofHom κT))]
    (u : T) (hu : IsUnit u) (hab : ∀ j, φ (a j).val = u * ψ (b j).val) :
    Blowup.Functor.Construction.affineBlowupMapTo I L φ hI ≫ ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap I κR a ha =
      Blowup.Functor.Construction.affineBlowupMapTo J L ψ hJ ≫ ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap J κS b hb := by
  let F := (Blowup.Functor.Construction.reesGradedMapTo I L φ hI).comp (ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap I κR a)
  let G := (Blowup.Functor.Construction.reesGradedMapTo J L ψ hJ).comp (ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap J κS b)
  have hF := HomogeneousIdeal.irrelevant_le_map_comp
    (ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap_irrelevant I κR a ha) (Blowup.Functor.Construction.reesGradedMapTo_irrelevant_le I L φ hI)
  have hG := HomogeneousIdeal.irrelevant_le_map_comp
    (ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap_irrelevant J κS b hb) (Blowup.Functor.Construction.reesGradedMapTo_irrelevant_le J L ψ hJ)
  have eF : Blowup.Functor.Construction.affineBlowupMapTo I L φ hI ≫ ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap I κR a ha =
      Proj.map F hF := (Proj.map_comp _ _ _ _).symm
  have eG : Blowup.Functor.Construction.affineBlowupMapTo J L ψ hJ ≫ ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap J κS b hb =
      Proj.map G hG := (Proj.map_comp _ _ _ _).symm
  have hoF : Proj.map F hF ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m =
      ReesGrading.Construction.affineBlowupToSpec L ≫ Spec.map (CommRingCat.ofHom κT) := by
    rw [← eF]
    exact reesProjectiveCoordinateMap_restriction_over I L κR κT φ hφκ hI a ha
  have hoG : Proj.map G hG ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m =
      ReesGrading.Construction.affineBlowupToSpec L ≫ Spec.map (CommRingCat.ofHom κT) := by
    rw [← eG]
    exact reesProjectiveCoordinateMap_restriction_over J L κS κT ψ hψκ hJ b hb
  let c := algebraMap T (reesAlgebra L) u
  let v := fun j : Fin (m + 1) => G (MvPolynomial.X j)
  let κ := (algebraMap T (reesAlgebra L)).comp κT
  have hGC (z : ℂ) : G (MvPolynomial.C z) = κ z := by
    change Blowup.Functor.Construction.reesGradedMapTo J L ψ hJ
      (ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap J κS b (MvPolynomial.C z)) = κ z
    rw [ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap_C, reesGradedMapTo_constants]
    exact congrArg (algebraMap T (reesAlgebra L)) (RingHom.congr_fun hψκ z)
  have hFC (z : ℂ) : F (MvPolynomial.C z) = κ z := by
    change Blowup.Functor.Construction.reesGradedMapTo I L φ hI
      (ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap I κR a (MvPolynomial.C z)) = κ z
    rw [ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap_C, reesGradedMapTo_constants]
    exact congrArg (algebraMap T (reesAlgebra L)) (RingHom.congr_fun hφκ z)
  have hFX (j : Fin (m + 1)) : F (MvPolynomial.X j) = c * v j := by
    dsimp only [F, G, v, c, GradedRingHom.comp_apply]
    rw [ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap_X, ReesProjectiveCoordinates.Construction.reesProjectivePolynomialMap_X,
      reesGradedMapTo_generator, reesGradedMapTo_generator]
    apply Subtype.ext
    change Polynomial.monomial 1 (φ (a j).val) =
      Polynomial.C u * Polynomial.monomial 1 (ψ (b j).val)
    rw [Polynomial.C_mul_monomial, hab j]
  have hFeval : F.toRingHom = MvPolynomial.eval₂Hom κ (fun j => c * v j) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      exact (hFC z).trans (MvPolynomial.eval₂Hom_C _ _ z).symm
    · intro j
      exact (hFX j).trans (MvPolynomial.eval₂Hom_X' κ (fun j => c * v j) j).symm
  have hGeval : G.toRingHom = MvPolynomial.eval₂Hom κ v := by
    apply MvPolynomial.ringHom_ext
    · intro z
      exact (hGC z).trans (MvPolynomial.eval₂Hom_C _ _ z).symm
    · intro j
      exact (MvPolynomial.eval₂Hom_X' κ v j).symm
  let : LocallyOfFiniteType (Proj.map F hF ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) := by
    rw [hoF]
    infer_instance
  rw [eF, eG]
  apply ProjectiveProportionalMaps.Construction.projMap_eq_of_homogeneous_units F G hF hG (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)
    (hoF.trans hoG.symm) (fun d => c ^ d)
    (fun d => (hu.map (algebraMap T (reesAlgebra L))).pow d)
  intro d p hp
  change F.toRingHom p = c ^ d * G.toRingHom p
  rw [hFeval, hGeval]
  exact HilbertScheme.Presentations.Dehomogenization.GradedHilbert.homogeneous_eval₂_scale κ v c hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ReesProjectiveComparison.Construction
