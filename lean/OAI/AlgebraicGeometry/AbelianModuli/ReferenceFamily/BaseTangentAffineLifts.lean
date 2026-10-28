import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.CoefficientDerivationSection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoefficientNaturality

/-! # Base Tangent Affine Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentAffineLifts

noncomputable section

/-! A single tangent derivation of the affine base constructs actual
dual-number lifts on each smooth affine family chart, linearly in that
base tangent. The original special-fiber and base-point maps are retained. -/

variable (k R S B : Type) [Field k] [CommRing R] [CommRing S] [CommRing B]
    [Algebra k R] [Algebra k S] [Algebra k B] [Algebra R S] [Algebra R k] [Algebra R B] [Algebra S B]
    [IsScalarTower k R S] [IsScalarTower k R k] [IsScalarTower k R B] [IsScalarTower k S B]
    [IsScalarTower R k B] [IsScalarTower R S B] [Algebra.FormallySmooth R S]

def baseTangentAffineDerivation : Derivation k R k →ₗ[k] Derivation k S B :=
  (Smooth.CoefficientDerivationSection.smoothCoefficientDerivationSection k R S B).comp
    (Dual.CoefficientLiftNaturality.coefficientDerivationMap k R k B (IsScalarTower.toAlgHom R k B))

def baseTangentAffineLift (d : Derivation k R k) : S →ₐ[k] DualNumber B :=
  Smooth.CoefficientDerivationSection.smoothLinearCoefficientLift k R S B
    (Dual.CoefficientLiftNaturality.coefficientDerivationMap k R k B (IsScalarTower.toAlgHom R k B) d)

theorem baseTangentAffineLift_snd (d : Derivation k R k) (s : S) :
    (baseTangentAffineLift k R S B d s).snd = baseTangentAffineDerivation k R S B d s :=
  Smooth.CoefficientDerivationSection.smoothLinearCoefficientLift_snd k R S B _ s

theorem baseTangentAffineLift_reduction (d : Derivation k R k) (s : S) :
    (baseTangentAffineLift k R S B d s).fst = algebraMap S B s :=
  AlgHom.congr_fun (Smooth.CoefficientDerivationSection.smoothLinearCoefficientLift_reduction k R S B
    (Dual.CoefficientLiftNaturality.coefficientDerivationMap k R k B (IsScalarTower.toAlgHom R k B) d)) s

theorem baseTangentAffineLift_base (d : Derivation k R k) (r : R) :
    baseTangentAffineLift k R S B d (algebraMap R S r) =
      Dual.NumberCoefficients.dualNumberRingMap (algebraMap k B) (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val r) := by
  have h := AlgHom.congr_fun (Smooth.CoefficientDerivationSection.smoothLinearCoefficientLift_base k R S B
    (Dual.CoefficientLiftNaturality.coefficientDerivationMap k R k B (IsScalarTower.toAlgHom R k B) d)) r
  have hn := AlgHom.congr_fun
    (Dual.AlgebraLiftCoefficientNaturality.dualAlgebraLiftDerivationEquiv_symm_natural k R k B (IsScalarTower.toAlgHom R k B) d) r
  exact h.trans hn

theorem baseTangentAffineLift_snd_add (d e : Derivation k R k) (s : S) :
    (baseTangentAffineLift k R S B (d + e) s).snd =
      (baseTangentAffineLift k R S B d s).snd + (baseTangentAffineLift k R S B e s).snd := by
  simp only [baseTangentAffineLift_snd, map_add, Derivation.add_apply]

theorem baseTangentAffineLift_snd_smul (a : k) (d : Derivation k R k) (s : S) :
    (baseTangentAffineLift k R S B (a • d) s).snd = a • (baseTangentAffineLift k R S B d s).snd := by
  simp only [baseTangentAffineLift_snd, map_smul, Derivation.smul_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentAffineLifts
