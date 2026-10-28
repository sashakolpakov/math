import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupCoefficientConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormalNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientMapSquares
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupLiftOpenCoordinates

/-! # Group Coefficient Conormal Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupCoefficientConormalNaturality

noncomputable section

/-! Conormal coordinates of actual group-valued lifts commute with
coefficient maps, through their actual translated affine lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C C' : Type) [CommRing k] [CommRing B] [CommRing C] [CommRing C']
    [Algebra k B] [Algebra k C] [Algebra k C'] [Algebra B C] [Algebra B C']
    [IsScalarTower k B C] [IsScalarTower k B C']
    [Algebra B k] [IsScalarTower k B k] [IsScalarTower B k C] [IsScalarTower B k C']
    {A : Over (Spec (.of k))} [GrpObj A]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left]
    (hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B k (IsScalarTower.toAlgHom k B k) ≫ i = 1)
    (q : C →ₐ[B] C') (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c})

def groupCoefficientRestrictedLift :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C') ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ f =
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫
        (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫ c)} :=
  GroupLiftOpenCoordinates.groupLiftRestricted (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C')
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C C' (q.restrictScalars k))
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)))
    (Dual.CoefficientMapSquares.dualCoefficientOrigin_natural k C C' (q.restrictScalars k)) c f

theorem groupCoefficientOpenLiftEquiv_natural :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫
      (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C i hi c f).val =
    (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C' i hi
      (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫ c)
      (groupCoefficientRestrictedLift k B C C' q c f)).val := by
  have : Mono i := Over.mono_of_mono_left i
  apply (cancel_mono i).mp
  have hf : (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C i hi c f).val ≫ i = f.val / c :=
    GroupLiftOpenCoordinates.groupLiftOpenEquiv_fac (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) i
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)) (GroupCoefficientConormal.affineGroupIdentity_coefficients k B C i hi) c f
  have hg : (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C' i hi
      (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫ c)
      (groupCoefficientRestrictedLift k B C C' q c f)).val ≫ i =
      (groupCoefficientRestrictedLift k B C C' q c f).val /
        (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫ c) :=
    GroupLiftOpenCoordinates.groupLiftOpenEquiv_fac (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C') i
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C' (IsScalarTower.toAlgHom k B C')) (GroupCoefficientConormal.affineGroupIdentity_coefficients k B C' i hi)
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫ c)
    (groupCoefficientRestrictedLift k B C C' q c f)
  rw [Category.assoc, hf, hg, GrpObj.comp_div]
  rfl

variable [Algebra.FormallySmooth k B]

theorem groupCoefficientConormalEquiv_natural (z : (RingHom.ker (algebraMap B k)).Cotangent) :
    GroupCoefficientConormal.groupCoefficientConormalEquiv k B C' i hi
      (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫ c)
      (groupCoefficientRestrictedLift k B C C' q c f) z =
      q (GroupCoefficientConormal.groupCoefficientConormalEquiv k B C i hi c f z) :=
  Affine.DualLiftConormalNaturality.affineDualLiftConormalEquiv_natural k B C C' q
    (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C i hi c f)
    (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C' i hi
      (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫ c)
      (groupCoefficientRestrictedLift k B C C' q c f))
    (groupCoefficientOpenLiftEquiv_natural k B C C' i hi q c f) z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupCoefficientConormalNaturality
