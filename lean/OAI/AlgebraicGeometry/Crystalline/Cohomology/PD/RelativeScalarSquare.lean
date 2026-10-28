import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.RelativeScalarMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence

/-! # Relative Scalar Square -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.RelativeScalarSquare.PDRelativeScalarSquare

noncomputable section

/-! # Commuting PD algebra squares give commuting relative form squares -/

open _root_.CategoryTheory

universe u

variable (W R S A B : Type u) [CommRing W] [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Algebra W R] [Algebra W S] [Algebra R A] [Algebra S B]
  (I : Ideal A) (δ : DividedPowers I) (J : Ideal B) (ε : DividedPowers J)

def selfMap (u : A →ₐ[R] A) (hu : DividedPowers.IsDPMorphism δ δ u.toRingHom) :
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (algebraMap W R)
        (DeRham.PDDeRham.complex R A I δ) ⟶
      NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (algebraMap W R)
        (DeRham.PDDeRham.complex R A I δ) :=
  ((ModuleCat.restrictScalars (algebraMap W R)).mapHomologicalComplex (.up ℕ)).map
    (DeRhamEquivalence.PDDeRhamEquivalence.complexMap (A := CommAlgCat.of R A) (B := CommAlgCat.of R A)
      (CommAlgCat.ofHom u) hu)

theorem selfMap_symbol (u : A →ₐ[R] A) (hu : DividedPowers.IsDPMorphism δ δ u.toRingHom)
    (n : ℕ) (a : A) (v : Fin n → A) :
    ((selfMap W R A I δ u hu).f n).hom (DeRham.PDDeRham.symbol R A I δ a v) =
      DeRham.PDDeRham.symbol R A I δ (u a) (u ∘ v) :=
  DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (A := CommAlgCat.of R A) (B := CommAlgCat.of R A)
    (CommAlgCat.ofHom u) hu n a v

variable (φ : R →+* S) (hW : ∀ w, φ (algebraMap W R w) = algebraMap W S w)
  (f g : A →+* B)
  (hfc : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
  (hgc : ∀ r, g (algebraMap R A r) = algebraMap S B (φ r))
  (hf : DividedPowers.IsDPMorphism δ ε f) (hg : DividedPowers.IsDPMorphism δ ε g)
  (u : A →ₐ[R] A) (v : B →ₐ[S] B)
  (hu : DividedPowers.IsDPMorphism δ δ u.toRingHom)
  (hv : DividedPowers.IsDPMorphism ε ε v.toRingHom)
  (hcomm : g.comp u.toRingHom = v.toRingHom.comp f)

include hcomm in
theorem square : selfMap W R A I δ u hu ≫
      RelativeScalarMap.PDRelativeScalarMap.complexMap W R S A B φ hW g hgc I δ J ε hg =
    RelativeScalarMap.PDRelativeScalarMap.complexMap W R S A B φ hW f hfc I δ J ε hf ≫
      selfMap W S B J ε v hv := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  let p := ((selfMap W R A I δ u hu).f n).hom.toAddMonoidHom
  let q := ((selfMap W S B J ε v hv).f n).hom.toAddMonoidHom
  let fm := ((RelativeScalarMap.PDRelativeScalarMap.complexMap W R S A B φ hW f hfc I δ J ε hf).f n).hom.toAddMonoidHom
  let gm := ((RelativeScalarMap.PDRelativeScalarMap.complexMap W R S A B φ hW g hgc I δ J ε hg).f n).hom.toAddMonoidHom
  have he : gm.comp p = q.comp fm := DeRhamSemilinearMap.PDDeRhamSemilinearMap.addHom_ext R A I δ n (gm.comp p) (q.comp fm) (by
    intro a t
    have hl := (congrArg gm (selfMap_symbol W R A I δ u hu n a t)).trans
      (RelativeScalarMap.PDRelativeScalarMap.symbol W R S A B φ hW g hgc I δ J ε hg n (u a) (u ∘ t))
    have hr := (congrArg q (RelativeScalarMap.PDRelativeScalarMap.symbol W R S A B φ hW f hfc I δ J ε hf n a t)).trans
      (selfMap_symbol W S B J ε v hv n (f a) (f ∘ t))
    have hm := congrArg₂ (DeRham.PDDeRham.symbol S B J ε) (RingHom.congr_fun hcomm a)
      (funext (fun i => RingHom.congr_fun hcomm (t i)))
    exact hl.trans (hm.trans hr.symm))
  exact LinearMap.ext (fun x => DFunLike.congr_fun he x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.RelativeScalarSquare.PDRelativeScalarSquare
