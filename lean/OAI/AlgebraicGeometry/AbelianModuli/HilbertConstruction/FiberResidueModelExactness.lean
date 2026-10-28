import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberScalar
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Extension
import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Fiber Residue Model Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberResidueModelExactness

noncomputable section

/-! Exactness after the actual scheme-fiber scalar map transfers to the
iterated local-ring and residue-field tensors used by cycle lifting. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem fiber_model_residue_exact
    (S : Scheme.{u}) (x : S) (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
    (h : (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D).ExactAt 1) :
    letI : Algebra Γ(S, ⊤) (S.presheaf.stalk x) :=
      (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
    (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex (S.presheaf.stalk x)
      (IsLocalRing.ResidueField (S.presheaf.stalk x))
      (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex Γ(S, ⊤) (S.presheaf.stalk x)
        (D.sc' 0 1 2))).Exact := by
  let a := (S.fromSpecResidueField x).appTop.hom
  let b := (Scheme.ΓSpecIso (S.residueField x)).hom.hom
  let G := ModuleCat.extendScalars b
  have : PreservesFiniteLimits G := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.bijective)
  have hsc : ((D.sc' 0 1 2).map (ModuleCat.extendScalars a)).Exact :=
    (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mp h
  have hc : ((D.sc' 0 1 2).map (ModuleCat.extendScalars (b.comp a))).Exact :=
    (ShortComplex.exact_iff_of_iso ((D.sc' 0 1 2).mapNatIso
      (ModuleCat.extendScalarsComp a b))).mpr (hsc.map G)
  have he : b.comp a = (S.Γevaluation x).hom :=
    congrArg (fun q : Γ(S, ⊤) ⟶ S.residueField x => q.hom)
      (FiberScalar.FiberScalarMaps.fromResidue_appTop S x)
  rw [he] at hc
  let : Algebra Γ(S, ⊤) (S.presheaf.stalk x) :=
    (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  exact Iterated.TensorExactness.iterated_tensor_exact_of_composite (D.sc' 0 1 2) hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberResidueModelExactness
