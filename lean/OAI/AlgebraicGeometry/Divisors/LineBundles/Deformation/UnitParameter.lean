import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.CenterPolynomial
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties

/-! # Unit Parameter -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.UnitParameter.BundleCycles

noncomputable section

section

/-! At parameter one, the constant center family is the original
center inclusion. This is proved on the actual Laurent evaluation map. -/

theorem laurentEvalOne_naturality {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (a : LaurentPolynomial R) :
    LaurentPolynomial.eval₂ (RingHom.id S) (1 : Sˣ) (AddMonoidAlgebra.mapRingHom ℤ f a) =
      f (LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ) a) := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | C_mul_T n r =>
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.mapRingHom_single,
      LaurentPolynomial.single_eq_C_mul_T]
    simp only [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T,
      one_zpow, Units.val_one, mul_one, RingHom.id_apply]

theorem deformationCenterPolynomialMap_eval_one {R S : Type} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) (hf : I ≤ RingHom.ker f) (a : Iff.BundleCycles.deformationAlgebra I) :
    Polynomial.eval 1 (CenterPolynomial.BundleCycles.deformationCenterPolynomialMap I f hf a) = f (Global.DeformationProperties.BundleCycles.deformationAtOne I a) := by
  have h := congrArg (LaurentPolynomial.eval₂ (RingHom.id S) (1 : Sˣ))
    (CenterPolynomial.BundleCycles.deformationCenterPolynomialMap_toLaurent I f hf a)
  rw [LaurentPolynomial.eval₂_toLaurent] at h
  exact h.trans (laurentEvalOne_naturality f a.val)

end

section

/-! Evaluation at one is a natural retraction of the genuine deformation
algebra diagram over the original structure presheaf. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

theorem deformationAtOne_naturality {R S : Type} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (φ : R →+* S) (hφ : I ≤ J.comap φ) :
    (Global.DeformationProperties.BundleCycles.deformationAtOne J).comp (Maps.BundleCycles.deformationMap I J φ hφ) = φ.comp (Global.DeformationProperties.BundleCycles.deformationAtOne I) := by
  ext a
  exact laurentEvalOne_naturality φ a.val

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def deformationOneDiagram : Global.Deformation.BundleCycles.deformationDiagram I ⟶ (toOpensFunctor X).op ⋙ X.presheaf where
  app U := CommRingCat.ofHom (Global.DeformationProperties.BundleCycles.deformationAtOne (I.ideal U.unop))
  naturality {U V} a := by
    apply CommRingCat.hom_ext
    exact deformationAtOne_naturality (I.ideal U.unop) (I.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map a)).hom
      (I.ideal_le_comap_ideal (toOpens_mono a.unop.le))

theorem deformationOneDiagram_over :
    Global.Deformation.BundleCycles.deformationDiagramMap I ≫ deformationOneDiagram I = 𝟙 _ := by
  ext U r
  exact DFunLike.congr_fun (Global.DeformationProperties.BundleCycles.deformationAtOne_algebraMap (I.ideal U.unop)) r

end

/-! At parameter one, every homomorphism from the actual deformation
algebra is determined by its coefficient map. No reducedness is needed. -/

variable {R S : Type} [CommRing R] [CommRing S]

theorem deformationAtOne_parameter (I : Ideal R) :
    Global.DeformationProperties.BundleCycles.deformationAtOne I (Iff.BundleCycles.deformationParameter I) = 1 := by
  change LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ) (LaurentPolynomial.T 1) = 1
  simp

theorem deformationRingHom_eq_at_one (I : Ideal R) (φ ψ : Iff.BundleCycles.deformationAlgebra I →+* S)
    (hc : φ.comp (algebraMap R (Iff.BundleCycles.deformationAlgebra I)) = ψ.comp (algebraMap R (Iff.BundleCycles.deformationAlgebra I)))
    (hφ : φ (Iff.BundleCycles.deformationParameter I) = 1) (hψ : ψ (Iff.BundleCycles.deformationParameter I) = 1) : φ = ψ := by
  have hp : φ.comp (GenericFiber.BundleCycles.polynomialToDeformation I).toRingHom =
      ψ.comp (GenericFiber.BundleCycles.polynomialToDeformation I).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      change φ (GenericFiber.BundleCycles.polynomialToDeformation I (Polynomial.C r)) = ψ (GenericFiber.BundleCycles.polynomialToDeformation I (Polynomial.C r))
      have hr : GenericFiber.BundleCycles.polynomialToDeformation I (Polynomial.C r) = algebraMap R (Iff.BundleCycles.deformationAlgebra I) r :=
        (GenericFiber.BundleCycles.polynomialToDeformation I).commutes r
      rw [hr]
      exact DFunLike.congr_fun hc r
    · change φ (GenericFiber.BundleCycles.polynomialToDeformation I Polynomial.X) = ψ (GenericFiber.BundleCycles.polynomialToDeformation I Polynomial.X)
      rw [GenericFiber.BundleCycles.polynomialToDeformation_X, hφ, hψ]
  ext a
  obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow a.val
  have ha : a * Iff.BundleCycles.deformationParameter I ^ n = GenericFiber.BundleCycles.polynomialToDeformation I q := by
    apply Subtype.ext
    change a.val * (Iff.BundleCycles.deformationParameter I ^ n : Iff.BundleCycles.deformationAlgebra I).val = q.toLaurent
    rw [GenericFiber.BundleCycles.deformationParameter_pow_val]
    exact hq.symm
  have hf := congrArg φ ha
  have hg := congrArg ψ ha
  simp only [map_mul, map_pow, hφ, hψ, one_pow, mul_one] at hf hg
  exact hf.trans ((DFunLike.congr_fun hp q).trans hg.symm)

theorem deformationRingHom_at_one (I : Ideal R) (φ : Iff.BundleCycles.deformationAlgebra I →+* S)
    (hφ : φ (Iff.BundleCycles.deformationParameter I) = 1) :
    φ = (φ.comp (algebraMap R (Iff.BundleCycles.deformationAlgebra I))).comp (Global.DeformationProperties.BundleCycles.deformationAtOne I) := by
  apply deformationRingHom_eq_at_one I
  · ext r
    exact (congrArg (fun a => φ (algebraMap R (Iff.BundleCycles.deformationAlgebra I) a)) (DFunLike.congr_fun (Global.DeformationProperties.BundleCycles.deformationAtOne_algebraMap I) r)).symm
  · exact hφ
  · simp only [RingHom.comp_apply, deformationAtOne_parameter, map_one]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.UnitParameter.BundleCycles
