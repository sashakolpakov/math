import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction

/-! # Inverse Twist -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.InverseTwist.InverseTwistScalarRestriction

noncomputable section

/-! # Cancellation of the original base twist by inverse scalar restriction -/

open _root_.CategoryTheory

universe u

variable {W R : Type u} [CommRing W] [CommRing R] (b : W →+* R) (e : W ≃+* W)

theorem inverse_comp : b = (b.comp e.toRingHom).comp e.symm.toRingHom :=
  RingHom.ext (fun w => (congrArg b (e.apply_symm_apply w)).symm)

def functorIso : ModuleCat.restrictScalars.{u} (b.comp e.toRingHom) ⋙
    ModuleCat.restrictScalars e.symm.toRingHom ≅ ModuleCat.restrictScalars b :=
  (ModuleCat.restrictScalarsComp' e.symm.toRingHom (b.comp e.toRingHom) b (inverse_comp b e)).symm

def complexIso (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    ((ModuleCat.restrictScalars e.symm.toRingHom).mapHomologicalComplex (.up ℕ)).obj
      (((ModuleCat.restrictScalars (b.comp e.toRingHom)).mapHomologicalComplex (.up ℕ)).obj K) ≅
    ((ModuleCat.restrictScalars b).mapHomologicalComplex (.up ℕ)).obj K :=
  (Functor.mapHomologicalComplexCompIso (functorIso b e) (.up ℕ)).app K

theorem component (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (x : K.X n) :
    ((complexIso b e K).hom.f n).hom x = x := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.InverseTwist.InverseTwistScalarRestriction
